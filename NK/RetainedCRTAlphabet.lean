import NK.RetainedFibers
import RK.LemmaC

/-! # Two-prime retained-word interval alphabets

CRT reduction followed by retaining every kth digit pulls an ordered paired-word
alphabet back to full residues. Every paired word has exactly
`(p*q)^((k-1)*e)` preimages, giving an exact interval-moment multiplier.
-/
namespace NK

abbrev RetainedPair := List ℕ × List ℕ

/-- CRT reduction followed by the two retained-digit projections. -/
def retainedPair (k p q e x : ℕ) : RetainedPair :=
  (retainedDigits k p e (x % p ^ (k * e)),
    retainedDigits k q e (x % q ^ (k * e)))

/-- The directed relation of the compressed two-prime graph. -/
def RetainedPairArc (k p q : ℕ) (v w : RetainedPair) : Prop :=
  v ≠ w ∧ (v.1 = w.1 ∨ FirstDifferencePowerArc k p v.1 w.1) ∧
    (v.2 = w.2 ∨ FirstDifferencePowerArc k q v.2 w.2)

private theorem powerArc_mod_or_eq (k M P x y : ℕ) (hP : P ∣ M)
    (h : PowerArc k M x y) : x % P = y % P ∨ PowerArc k P (x % P) (y % P) := by
  by_cases he : x % P = y % P
  · exact Or.inl he
  · obtain ⟨_, z, hz⟩ := h
    refine Or.inr ⟨he, z, ?_⟩
    simpa only [Nat.ModEq, Nat.mod_add_mod, Nat.mod_mod] using (Nat.ModEq.of_dvd hP hz)

/-- A full power arc induces exactly the weak coordinate relations and a strict
change in at least one projected coordinate. -/
theorem powerArc_retainedPair (k p q e x y : ℕ) (hk : 1 ≤ k)
    (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e)
    (hx : x < (p * q) ^ (k * e)) (hy : y < (p * q) ^ (k * e))
    (harc : PowerArc k ((p * q) ^ (k * e)) x y) :
    RetainedPairArc k p q (retainedPair k p q e x) (retainedPair k p q e y) := by
  have hP : 0 < p ^ (k * e) := pow_pos hp.pos _
  have hQ : 0 < q ^ (k * e) := pow_pos hq.pos _
  have hpc : p ^ (k * e) ∣ (p * q) ^ (k * e) := by rw [mul_pow]; exact dvd_mul_right _ _
  have hqc : q ^ (k * e) ∣ (p * q) ^ (k * e) := by rw [mul_pow]; exact dvd_mul_left _ _
  have hrp := powerArc_mod_or_eq k _ (p ^ (k * e)) x y hpc harc
  have hrq := powerArc_mod_or_eq k _ (q ^ (k * e)) x y hqc harc
  have hpword : (retainedPair k p q e x).1 = (retainedPair k p q e y).1 ∨
      FirstDifferencePowerArc k p (retainedPair k p q e x).1 (retainedPair k p q e y).1 := by
    rcases hrp with h | h
    · exact Or.inl (congrArg (retainedDigits k p e) h)
    · exact Or.inr (powerArc_retainedDigits k p e _ _ hk hp he
        (Nat.mod_lt _ hP) (Nat.mod_lt _ hP) h)
  have hqword : (retainedPair k p q e x).2 = (retainedPair k p q e y).2 ∨
      FirstDifferencePowerArc k q (retainedPair k p q e x).2 (retainedPair k p q e y).2 := by
    rcases hrq with h | h
    · exact Or.inl (congrArg (retainedDigits k q e) h)
    · exact Or.inr (powerArc_retainedDigits k q e _ _ hk hq he
        (Nat.mod_lt _ hQ) (Nat.mod_lt _ hQ) h)
  refine ⟨?_, hpword, hqword⟩
  intro hpair
  have hxp : x % p ^ (k * e) = y % p ^ (k * e) := by
    rcases hrp with h | h
    · exact h
    · exact False.elim ((powerArc_retainedDigits k p e _ _ hk hp he
        (Nat.mod_lt _ hP) (Nat.mod_lt _ hP) h).ne (congrArg Prod.fst hpair))
  have hxq : x % q ^ (k * e) = y % q ^ (k * e) := by
    rcases hrq with h | h
    · exact h
    · exact False.elim ((powerArc_retainedDigits k q e _ _ hk hq he
        (Nat.mod_lt _ hQ) (Nat.mod_lt _ hQ) h).ne (congrArg Prod.snd hpair))
  apply harc.1
  exact KthPower.crt_injOn _ _ (hco.pow _ _)
    (by simpa [mul_pow] using hx) (by simpa [mul_pow] using hy) (Prod.ext hxp hxq)

/-- The exact fiber of a paired retained word, counted by CRT and the single-prime fibers. -/
theorem retainedPair_fiber_card (k p q e : ℕ) (w : RetainedPair)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hq : 2 ≤ q) (hco : p.Coprime q)
    (hlenp : w.1.length = e) (hlenq : w.2.length = e)
    (hvalidp : ∀ a ∈ w.1, a < p) (hvalidq : ∀ a ∈ w.2, a < q) :
    ((Finset.range ((p * q) ^ (k * e))).filter
      (fun x => retainedPair k p q e x = w)).card = (p * q) ^ ((k - 1) * e) := by
  have hP : 0 < p ^ (k * e) := pow_pos (by omega) _
  have hQ : 0 < q ^ (k * e) := pow_pos (by omega) _
  have hset : (Finset.range ((p * q) ^ (k * e))).filter
      (fun x => retainedPair k p q e x = w) =
      KthPower.crtBlock (p ^ (k * e)) (q ^ (k * e))
        (retainedFiber k p w.1) (retainedFiber k q w.2) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, KthPower.mem_crtBlock,
      mem_retainedFiber, hlenp, hlenq, retainedPair, Prod.ext_iff, mul_pow]
    simp only [Nat.mod_lt _ hP, Nat.mod_lt _ hQ, true_and]
  rw [hset, KthPower.crtBlock_card _ _ (hco.pow _ _)
    (retainedFiber k p w.1) (retainedFiber k q w.2)
    (fun x hx => by simpa only [hlenp] using (mem_retainedFiber k p x w.1).mp hx |>.1)
    (fun x hx => by simpa only [hlenq] using (mem_retainedFiber k q x w.2).mp hx |>.1)]
  rw [retainedFiber_card k p w.1 hk hp hvalidp, retainedFiber_card k q w.2 hk hq hvalidq,
    hlenp, hlenq, mul_pow]

/-- The full-residue support over a finite set of paired words. -/
def retainedPairPreimage (k p q e : ℕ) (W : Finset RetainedPair) : Finset ℕ :=
  (Finset.range ((p * q) ^ (k * e))).filter (fun x => retainedPair k p q e x ∈ W)

/-- Every real weight on paired words acquires the exact CRT free-digit multiplicity. -/
theorem sum_retainedPairPreimage (k p q e : ℕ) (W : Finset RetainedPair)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hq : 2 ≤ q) (hco : p.Coprime q)
    (hlenp : ∀ w ∈ W, w.1.length = e) (hlenq : ∀ w ∈ W, w.2.length = e)
    (hvalidp : ∀ w ∈ W, ∀ a ∈ w.1, a < p) (hvalidq : ∀ w ∈ W, ∀ a ∈ w.2, a < q)
    (g : RetainedPair → ℝ) :
    ∑ x ∈ retainedPairPreimage k p q e W, g (retainedPair k p q e x) =
      (((p * q) ^ ((k - 1) * e) : ℕ) : ℝ) * ∑ w ∈ W, g w := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := retainedPairPreimage k p q e W) (t := W) (g := retainedPair k p q e)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2) (fun x => g (retainedPair k p q e x))
  rw [← hgroup, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hfiber : ((retainedPairPreimage k p q e W).filter
      (fun x => retainedPair k p q e x = w)) =
      (Finset.range ((p * q) ^ (k * e))).filter (fun x => retainedPair k p q e x = w) := by
    ext x
    simp only [retainedPairPreimage, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, heq ▸ hw⟩, heq⟩
  calc
    _ = ∑ _x ∈ (retainedPairPreimage k p q e W).filter
        (fun x => retainedPair k p q e x = w), g w := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (((retainedPairPreimage k p q e W).filter
        (fun x => retainedPair k p q e x = w)).card : ℝ) * g w := by simp [nsmul_eq_mul]
    _ = _ := by
      rw [hfiber, retainedPair_fiber_card k p q e w hk hp hq hco
        (hlenp w hw) (hlenq w hw) (hvalidp w hw) (hvalidq w hw)]

/-- Cardinality form of the uniform CRT fiber identity. -/
theorem retainedPairPreimage_card (k p q e : ℕ) (W : Finset RetainedPair)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hq : 2 ≤ q) (hco : p.Coprime q)
    (hlenp : ∀ w ∈ W, w.1.length = e) (hlenq : ∀ w ∈ W, w.2.length = e)
    (hvalidp : ∀ w ∈ W, ∀ a ∈ w.1, a < p) (hvalidq : ∀ w ∈ W, ∀ a ∈ w.2, a < q) :
    (retainedPairPreimage k p q e W).card = (p * q) ^ ((k - 1) * e) * W.card := by
  have h := sum_retainedPairPreimage k p q e W hk hp hq hco hlenp hlenq
    hvalidp hvalidq (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- Finite interval data on the actual paired retained-word graph. -/
structure RetainedPairAlphabet (k p q e : ℕ) where
  support : Finset RetainedPair
  left_length : ∀ w ∈ support, w.1.length = e
  right_length : ∀ w ∈ support, w.2.length = e
  left_valid : ∀ w ∈ support, ∀ a ∈ w.1, a < p
  right_valid : ∀ w ∈ support, ∀ a ∈ w.2, a < q
  interval : (w : RetainedPair) → w ∈ support → UnitInterval
  ordered : ∀ v (hv : v ∈ support) w (hw : w ∈ support), RetainedPairArc k p q v w →
    (interval v hv).left + (interval v hv).width ≤ (interval w hw).left

namespace RetainedPairAlphabet

variable {k p q e : ℕ}

/-- The moment of the finite compressed alphabet, before free digits are restored. -/
noncomputable def moment (A : RetainedPairAlphabet k p q e) (f : ℝ) : ℝ :=
  ∑ w ∈ A.support.attach, (A.interval w.val w.property).width ^ f

/-- Restoring the discarded digits and applying CRT gives a full modular interval alphabet. -/
noncomputable def toIntervalAlphabet (A : RetainedPairAlphabet k p q e)
    (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e) :
    IntervalAlphabet k ((p * q) ^ (k * e)) where
  support := retainedPairPreimage k p q e A.support
  residue_lt := fun x hx => Finset.mem_range.mp (Finset.mem_filter.mp hx).1
  interval := fun x hx => A.interval (retainedPair k p q e x) (Finset.mem_filter.mp hx).2
  ordered := by
    intro x hx y hy harc
    exact A.ordered _ (Finset.mem_filter.mp hx).2 _ (Finset.mem_filter.mp hy).2
      (powerArc_retainedPair k p q e x y hk hp hq hco he
        (Finset.mem_range.mp (Finset.mem_filter.mp hx).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hy).1) harc)

/-- Each full residue receives exactly its compressed interval. -/
@[simp] theorem toIntervalAlphabet_interval (A : RetainedPairAlphabet k p q e)
    (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e)
    (x : ℕ) (hx : x ∈ (A.toIntervalAlphabet hk hp hq hco he).support) :
    (A.toIntervalAlphabet hk hp hq hco he).interval x hx =
      A.interval (retainedPair k p q e x) (Finset.mem_filter.mp hx).2 := rfl

/-- In particular, restoring free digits does not rescale any individual width. -/
theorem toIntervalAlphabet_width (A : RetainedPairAlphabet k p q e)
    (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e)
    (x : ℕ) (hx : x ∈ (A.toIntervalAlphabet hk hp hq hco he).support) :
    ((A.toIntervalAlphabet hk hp hq hco he).interval x hx).width =
      (A.interval (retainedPair k p q e x) (Finset.mem_filter.mp hx).2).width := rfl

/-- The exact free-digit and CRT multiplicity of the lifted support. -/
theorem toIntervalAlphabet_card (A : RetainedPairAlphabet k p q e)
    (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e) :
    (A.toIntervalAlphabet hk hp hq hco he).support.card =
      (p * q) ^ ((k - 1) * e) * A.support.card :=
  retainedPairPreimage_card k p q e A.support hk hp.two_le hq.two_le hco
    A.left_length A.right_length A.left_valid A.right_valid

/-- The exact moment identity for the full two-prime interval alphabet. -/
theorem toIntervalAlphabet_moment (A : RetainedPairAlphabet k p q e)
    (hk : 1 ≤ k) (hp : p.Prime) (hq : q.Prime) (hco : p.Coprime q) (he : 1 ≤ e)
    (f : ℝ) :
    (A.toIntervalAlphabet hk hp hq hco he).moment f =
      (((p * q) ^ ((k - 1) * e) : ℕ) : ℝ) * A.moment f := by
  classical
  let g : RetainedPair → ℝ := fun w =>
    if hw : w ∈ A.support then (A.interval w hw).width ^ f else 0
  have hg (w : RetainedPair) (hw : w ∈ A.support) :
      g w = (A.interval w hw).width ^ f := by simp only [g, dif_pos hw]
  have hlow : (∑ w ∈ A.support, g w) = A.moment f := by
    rw [← Finset.sum_attach A.support g]
    unfold moment
    apply Finset.sum_congr rfl
    intro w _
    exact hg w.val w.property
  have hlift : (A.toIntervalAlphabet hk hp hq hco he).moment f =
      ∑ x ∈ retainedPairPreimage k p q e A.support, g (retainedPair k p q e x) := by
    rw [← Finset.sum_attach (retainedPairPreimage k p q e A.support)
      (fun x => g (retainedPair k p q e x))]
    unfold IntervalAlphabet.moment
    apply Finset.sum_congr rfl
    intro x _
    exact (hg _ (Finset.mem_filter.mp x.property).2).symm
  rw [hlift, sum_retainedPairPreimage k p q e A.support hk hp.two_le hq.two_le hco
    A.left_length A.right_length A.left_valid A.right_valid g, hlow]

end RetainedPairAlphabet
end NK
