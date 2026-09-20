import NK.RetainedDigits

/-! # Exact fibers of the retained-digit projection

Fixing the `e` retained digits leaves exactly `(k-1)*e` base-`p` digits free.
The proof splits at `p^k`, using the one-level count already proved in RK.
No primality or squarefreeness assumption is needed for this counting fact.
-/
namespace NK

/-- Peeling one group of `k` original digits removes the first retained digit. -/
theorem retainedDigits_succ (k p e x : ℕ) :
    retainedDigits k p (e + 1) x = x % p :: retainedDigits k p e (x / p ^ k) := by
  have hstep (j : Fin e) :
      KthPower.digit p (k * j.succ.val) x =
        KthPower.digit p (k * j.val) (x / p ^ k) := by
    unfold KthPower.digit
    rw [Nat.div_div_eq_div_mul, ← pow_add]
    congr 2
    simp only [Fin.val_succ]
    ring
  simp only [retainedDigits, List.ofFn_succ, Fin.val_zero, Nat.mul_zero]
  rw [show KthPower.digit p 0 x = x % p by simp [KthPower.digit]]
  congr 1
  exact congrArg List.ofFn (funext hstep)

/-- The full residues having a prescribed retained word. -/
def retainedFiber (k p : ℕ) (w : List ℕ) : Finset ℕ :=
  (Finset.range (p ^ (k * w.length))).filter
    (fun x => retainedDigits k p w.length x = w)

@[simp] theorem mem_retainedFiber (k p x : ℕ) (w : List ℕ) :
    x ∈ retainedFiber k p w ↔
      x < p ^ (k * w.length) ∧ retainedDigits k p w.length x = w := by
  simp [retainedFiber]

/-- Splitting one group gives the retained head and the tail fiber. -/
theorem mem_retainedFiber_cons (k p x a : ℕ) (w : List ℕ) (hp : 0 < p) :
    x ∈ retainedFiber k p (a :: w) ↔ x % p = a ∧ x / p ^ k ∈ retainedFiber k p w := by
  have hsplit : p ^ (k * w.length) * p ^ k = p ^ (k * (w.length + 1)) := by
    rw [← pow_add]
    congr 1
  have hsize : x < p ^ (k * (w.length + 1)) ↔ x / p ^ k < p ^ (k * w.length) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp k), hsplit]
  simp only [mem_retainedFiber, List.length_cons, retainedDigits_succ,
    List.cons.injEq, hsize]
  tauto

/-- At one level, fixing the retained residue leaves `k-1` free digits. -/
theorem retained_bottom_card (k p a : ℕ) (hk : 1 ≤ k) (ha : a < p) :
    ((Finset.range (p ^ k)).filter (fun x => x % p = a)).card = p ^ (k - 1) := by
  have hset : (Finset.range (p ^ k)).filter (fun x => x % p = a) =
      KthPower.liftBlock k p 1 {a} := by
    ext x
    simp [KthPower.liftBlock, KthPower.digit]
  rw [hset, KthPower.liftBlock_card k p 1 {a} hk (by simpa using ha)]
  simp

/-- The tail split is a literal bijection with the bottom residue and tail fiber. -/
theorem retainedFiber_cons_card (k p a : ℕ) (w : List ℕ)
    (hk : 1 ≤ k) (hp : 0 < p) (ha : a < p) :
    (retainedFiber k p (a :: w)).card = p ^ (k - 1) * (retainedFiber k p w).card := by
  let B := (Finset.range (p ^ k)).filter (fun u => u % p = a)
  have hpk : 0 < p ^ k := pow_pos hp k
  have hpdvd : p ∣ p ^ k := dvd_pow_self p (by omega)
  have hsplit : ∀ u v : ℕ, u < p ^ k →
      (u + p ^ k * v) % p ^ k = u ∧ (u + p ^ k * v) / p ^ k = v := by
    intro u v hu
    exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu],
      by rw [Nat.add_mul_div_left _ _ hpk, Nat.div_eq_of_lt hu, Nat.zero_add]⟩
  have hbij : (retainedFiber k p (a :: w)).card = (B ×ˢ retainedFiber k p w).card := by
    refine Finset.card_nbij' (fun x => (x % p ^ k, x / p ^ k))
      (fun q => q.1 + p ^ k * q.2) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      rw [mem_retainedFiber_cons k p x a w hp] at hx
      rw [Finset.mem_product]
      refine ⟨?_, hx.2⟩
      simp only [B, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt _ hpk, by rw [Nat.mod_mod_of_dvd _ hpdvd]; exact hx.1⟩
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_coe, Finset.mem_product] at huv ⊢
      obtain ⟨hu, hv⟩ := huv
      have hu' : u < p ^ k ∧ u % p = a := by simpa [B] using hu
      obtain ⟨hmod, hdiv⟩ := hsplit u v hu'.1
      rw [mem_retainedFiber_cons k p _ a w hp, hdiv]
      refine ⟨?_, hv⟩
      rw [← Nat.mod_mod_of_dvd _ hpdvd, hmod]
      exact hu'.2
    · intro x _
      exact Nat.mod_add_div x (p ^ k)
    · rintro ⟨u, v⟩ huv
      simp only [Finset.mem_coe, Finset.mem_product] at huv
      have hu : u < p ^ k := (Finset.mem_filter.mp huv.1).1 |> Finset.mem_range.mp
      obtain ⟨hmod, hdiv⟩ := hsplit u v hu
      simp [hmod, hdiv]
  rw [hbij, Finset.card_product, retained_bottom_card k p a hk ha]

/-- Every valid retained word has exactly `p^((k-1)*length)` preimages. -/
theorem retainedFiber_card (k p : ℕ) (w : List ℕ) (hk : 1 ≤ k) (hp : 2 ≤ p)
    (hw : ∀ a ∈ w, a < p) :
    (retainedFiber k p w).card = p ^ ((k - 1) * w.length) := by
  induction w with
  | nil =>
    have hset : retainedFiber k p [] = {0} := by
      ext x
      simp [retainedFiber, retainedDigits]
    simp [hset]
  | cons a w ih =>
    have ha : a < p := hw a List.mem_cons_self
    have htail : ∀ b ∈ w, b < p := fun b hb => hw b (List.mem_cons_of_mem _ hb)
    rw [retainedFiber_cons_card k p a w hk (by omega) ha, ih htail]
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, pow_add]
    exact Nat.mul_comm _ _

/-- Fixed-length formulation of the exact fiber count. -/
theorem retainedDigits_fiber_card (k p e : ℕ) (w : List ℕ)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hlen : w.length = e) (hw : ∀ a ∈ w, a < p) :
    ((Finset.range (p ^ (k * e))).filter (fun x => retainedDigits k p e x = w)).card =
      p ^ ((k - 1) * e) := by
  simpa only [retainedFiber, hlen] using retainedFiber_card k p w hk hp hw

/-- Full preimage of a finite collection of retained words. -/
def retainedPreimage (k p e : ℕ) (W : Finset (List ℕ)) : Finset ℕ :=
  (Finset.range (p ^ (k * e))).filter (fun x => retainedDigits k p e x ∈ W)

/-- Distinct words have disjoint fibers, so finite selected-word counts multiply. -/
theorem retainedPreimage_card (k p e : ℕ) (W : Finset (List ℕ))
    (hk : 1 ≤ k) (hp : 2 ≤ p)
    (hlen : ∀ w ∈ W, w.length = e) (hvalid : ∀ w ∈ W, ∀ a ∈ w, a < p) :
    (retainedPreimage k p e W).card = p ^ ((k - 1) * e) * W.card := by
  classical
  have hcount := Finset.card_eq_sum_card_fiberwise
    (f := retainedDigits k p e) (s := retainedPreimage k p e W) (t := W)
    (by
      intro x hx
      exact (Finset.mem_filter.mp hx).2)
  have hfiber (w : List ℕ) (hw : w ∈ W) :
      ((retainedPreimage k p e W).filter (fun x => retainedDigits k p e x = w)) =
        (Finset.range (p ^ (k * e))).filter (fun x => retainedDigits k p e x = w) := by
    ext x
    simp only [retainedPreimage, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, heq ▸ hw⟩, heq⟩
  rw [hcount]
  calc
    _ = W.card * p ^ ((k - 1) * e) := Finset.sum_const_nat (fun w hw => by
      rw [hfiber w hw]
      exact retainedDigits_fiber_card k p e w hk hp (hlen w hw) (hvalid w hw))
    _ = _ := Nat.mul_comm _ _

/-- Every valid low word occurs as a retained word of a bounded full residue. -/
theorem exists_retainedDigits_eq (k p e : ℕ) (w : List ℕ)
    (hk : 1 ≤ k) (hp : 2 ≤ p) (hlen : w.length = e) (hw : ∀ a ∈ w, a < p) :
    ∃ x : ℕ, x < p ^ (k * e) ∧ retainedDigits k p e x = w := by
  have hc := retainedDigits_fiber_card k p e w hk hp hlen hw
  have hpos : 0 < ((Finset.range (p ^ (k * e))).filter
      (fun x => retainedDigits k p e x = w)).card := by
    rw [hc]
    exact pow_pos (by omega) _
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact ⟨x, by simpa using hx⟩

/-- Every real weight on retained words is repeated by the exact free-digit
multiplicity. This specializes directly to the interval-moment identity. -/
theorem sum_retainedPreimage (k p e : ℕ) (W : Finset (List ℕ))
    (hk : 1 ≤ k) (hp : 2 ≤ p)
    (hlen : ∀ w ∈ W, w.length = e) (hvalid : ∀ w ∈ W, ∀ a ∈ w, a < p)
    (g : List ℕ → ℝ) :
    ∑ x ∈ retainedPreimage k p e W, g (retainedDigits k p e x) =
      ((p ^ ((k - 1) * e) : ℕ) : ℝ) * ∑ w ∈ W, g w := by
  classical
  have hgroup := Finset.sum_fiberwise_of_maps_to
    (s := retainedPreimage k p e W) (t := W) (g := retainedDigits k p e)
    (by intro x hx; exact (Finset.mem_filter.mp hx).2)
    (fun x => g (retainedDigits k p e x))
  rw [← hgroup, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hfiber :
      ((retainedPreimage k p e W).filter (fun x => retainedDigits k p e x = w)) =
        (Finset.range (p ^ (k * e))).filter (fun x => retainedDigits k p e x = w) := by
    ext x
    simp only [retainedPreimage, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hx, heq⟩
      exact ⟨⟨hx, heq ▸ hw⟩, heq⟩
  calc
    _ = ∑ _x ∈ (retainedPreimage k p e W).filter
        (fun x => retainedDigits k p e x = w), g w := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (((retainedPreimage k p e W).filter
        (fun x => retainedDigits k p e x = w)).card : ℝ) * g w := by
      simp [nsmul_eq_mul]
    _ = _ := by
      rw [hfiber, retainedDigits_fiber_card k p e w hk hp (hlen w hw) (hvalid w hw)]

end NK
