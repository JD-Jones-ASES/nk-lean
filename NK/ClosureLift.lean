import NK.Definitions
import NK.PerfectPowerClosure

/-! # Free copying from an arbitrary modulus to its perfect-power closure

Reduction modulo d sends every nontrivial kth-power arc at the canonical
closure to a nontrivial kth-power arc modulo d. Thus an interval alphabet
can be copied unchanged to every residue above each seed vertex.
-/

namespace NK

/-- A nontrivial closure-level power arc cannot collapse under reduction. -/
theorem powerArc_mod_perfectPowerClosure (k d x y : ℕ)
    (hk : 1 ≤ k) (hd : 1 ≤ d)
    (hx : x < perfectPowerClosure k d) (hy : y < perfectPowerClosure k d)
    (h : PowerArc k (perfectPowerClosure k d) x y) :
    PowerArc k d (x % d) (y % d) := by
  obtain ⟨hne, z, hz⟩ := h
  have hB : Nat.ModEq (perfectPowerClosure k d) (x + z ^ k) y := hz
  have hmod : Nat.ModEq d (x + z ^ k) y :=
    hB.of_dvd (dvd_perfectPowerClosure k d hk hd)
  refine ⟨?_, z, ?_⟩
  · intro heq
    have hxy : Nat.ModEq d x y := heq
    have hzero : Nat.ModEq d (z ^ k) 0 :=
      hxy.add_left_cancel (by simpa using hmod)
    have hdiv : perfectPowerClosure k d ∣ z ^ k :=
      perfectPowerClosure_dvd_of_dvd_pow k d z hk hd
        (Nat.modEq_zero_iff_dvd.mp hzero)
    have heqB : x % perfectPowerClosure k d = y % perfectPowerClosure k d := by
      simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv] using hz
    exact hne (by simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using heqB)
  · exact ((Nat.mod_modEq x d).add_right (z ^ k)).trans
      (hmod.trans (Nat.mod_modEq y d).symm)

/-- Residue copying is the image of the seed support times a full fiber. -/
theorem residueCopies_eq_image (d B : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ B)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r < d) :
    (Finset.range B).filter (fun x => x % d ∈ S) =
      (S ×ˢ Finset.range (B / d)).image (fun p => p.1 + d * p.2) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_product]
  constructor
  · intro hx
    refine ⟨(x % d, x / d), ⟨hx.2, ?_⟩, Nat.mod_add_div x d⟩
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < d), Nat.div_mul_cancel hdiv]
    exact hx.1
  · rintro ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    have hrlt := hS r hr
    have ht' : d * (t + 1) ≤ B := by
      calc
        d * (t + 1) ≤ d * (B / d) := Nat.mul_le_mul_left d (by omega)
        _ = B := Nat.mul_div_cancel' hdiv
    refine ⟨by nlinarith, ?_⟩
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrlt] using hr

/-- The pair (seed residue, fiber index) gives each copied residue exactly once. -/
theorem residueCopies_injective (d q : ℕ) (hd : 1 ≤ d)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r < d) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + d * p.2)
      (↑(S ×ˢ Finset.range q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  have ha' := (Finset.mem_product.mp ha).1
  have hb' := (Finset.mem_product.mp hb).1
  have hfirst : a.1 = b.1 := by
    have hm := congrArg (fun x => x % d) hab
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hS _ ha'),
      Nat.mod_eq_of_lt (hS _ hb')] using hm
  apply Prod.ext hfirst
  apply Nat.mul_left_cancel (by omega : 0 < d)
  change a.1 + d * a.2 = b.1 + d * b.2 at hab
  omega

/-- An arbitrary real weight, constant on each residue fiber, gains the fiber multiplicity. -/
theorem sum_residueCopies (d B : ℕ) (hd : 1 ≤ d) (hdiv : d ∣ B)
    (S : Finset ℕ) (hS : ∀ r ∈ S, r < d) (w : ℕ → ℝ) :
    (∑ x ∈ (Finset.range B).filter (fun x => x % d ∈ S), w (x % d)) =
      (B / d : ℕ) * ∑ r ∈ S, w r := by
  rw [residueCopies_eq_image d B hd hdiv S hS,
    Finset.sum_image (residueCopies_injective d (B / d) hd S hS), Finset.sum_product]
  have heq : (∑ r ∈ S, ∑ t ∈ Finset.range (B / d), w ((r + d * t) % d)) =
      ∑ r ∈ S, ∑ _t ∈ Finset.range (B / d), w r := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro t _ht
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hS r hr)]
  rw [heq]
  simp [← Finset.mul_sum]

namespace IntervalAlphabet

/-- Every residue in the closure whose reduction belongs to the seed support. -/
def closureLiftSupport {k d : ℕ} (A : IntervalAlphabet k d) : Finset ℕ :=
  (Finset.range (perfectPowerClosure k d)).filter fun x => x % d ∈ A.support

@[simp] theorem mem_closureLiftSupport {k d x : ℕ} (A : IntervalAlphabet k d) :
    x ∈ A.closureLiftSupport ↔ x < perfectPowerClosure k d ∧ x % d ∈ A.support := by
  simp [closureLiftSupport]

/-- Copy the seed interval to every residue in its canonical closure fiber. -/
noncomputable def closureLift {k d : ℕ} (A : IntervalAlphabet k d)
    (hk : 1 ≤ k) (hd : 1 ≤ d) : IntervalAlphabet k (perfectPowerClosure k d) where
  support := A.closureLiftSupport
  residue_lt := fun _ hx => (A.mem_closureLiftSupport.mp hx).1
  interval := fun x hx => A.interval (x % d) (A.mem_closureLiftSupport.mp hx).2
  ordered := by
    intro x hx y hy hxy
    exact A.ordered _ _ _ _ (powerArc_mod_perfectPowerClosure k d x y hk hd
      (A.mem_closureLiftSupport.mp hx).1 (A.mem_closureLiftSupport.mp hy).1 hxy)

/-- Every seed vertex has exactly B/d copies in the lifted support. -/
theorem closureLift_card {k d : ℕ} (A : IntervalAlphabet k d)
    (hk : 1 ≤ k) (hd : 1 ≤ d) :
    (A.closureLift hk hd).support.card =
      (perfectPowerClosure k d / d) * A.support.card := by
  change A.closureLiftSupport.card = _
  rw [closureLiftSupport,
    residueCopies_eq_image d (perfectPowerClosure k d) hd
      (dvd_perfectPowerClosure k d hk hd) A.support A.residue_lt,
    Finset.card_image_of_injOn
      (residueCopies_injective d (perfectPowerClosure k d / d) hd A.support A.residue_lt),
    Finset.card_product, Finset.card_range, Nat.mul_comm]

/-- Every interval moment is multiplied by the exact number of free copies.
The identity holds for every real f, since it merely counts identical widths. -/
theorem closureLift_moment {k d : ℕ} (A : IntervalAlphabet k d)
    (hk : 1 ≤ k) (hd : 1 ≤ d) (f : ℝ) :
    (A.closureLift hk hd).moment f =
      (perfectPowerClosure k d / d : ℕ) * A.moment f := by
  classical
  let w : ℕ → ℝ := fun r => if hr : r ∈ A.support then (A.interval r hr).width ^ f else 0
  have hseed : A.moment f = ∑ r ∈ A.support, w r := by
    rw [moment, ← Finset.sum_attach A.support w]
    apply Finset.sum_congr rfl
    intro x _hx
    simp only [w, dif_pos x.property]
  have hlift : (A.closureLift hk hd).moment f =
      ∑ x ∈ A.closureLiftSupport, w (x % d) := by
    rw [moment, ← Finset.sum_attach A.closureLiftSupport (fun x => w (x % d))]
    apply Finset.sum_congr rfl
    intro x _hx
    have hm : x.val % d ∈ A.support := (A.mem_closureLiftSupport.mp x.property).2
    simp only [closureLift, w, dif_pos hm]
  rw [hlift, hseed, closureLiftSupport]
  exact sum_residueCopies d (perfectPowerClosure k d) hd
    (dvd_perfectPowerClosure k d hk hd) A.support A.residue_lt w

end IntervalAlphabet
end NK
