import NK.GraphIntervals

/-! # Exact interval-moment capacity of directed lexicographic products

For finite vertex types the supremum is taken over ordinary positive interval
alphabets. Products are constructed by nesting. The reverse inequality uses
actual occupied-fiber hulls and normalization. Empty graphs and loops are
allowed. The theorem holds for f≥0, including the requested f>0 domain.
-/
namespace NK.LexicographicCapacity

universe u v
open DigraphAlphabet

variable {V : Type u} {W : Type v} [Fintype V] [Fintype W]
variable (G : V → V → Prop) (H : W → W → Prop)

def momentSet (f : ℝ) : Set ℝ := {z | ∃ A : DigraphAlphabet G, A.moment f = z}

noncomputable def capacity (f : ℝ) : ℝ := sSup (momentSet G f)

theorem momentSet_nonempty (f : ℝ) : (momentSet G f).Nonempty :=
  ⟨0, DigraphAlphabet.empty G, empty_moment f⟩

theorem momentSet_bddAbove (f : ℝ) (hf : 0 ≤ f) : BddAbove (momentSet G f) := by
  refine ⟨(Fintype.card V : ℝ), ?_⟩
  rintro z ⟨A,rfl⟩
  exact A.moment_le_card f hf

theorem moment_le_capacity (f : ℝ) (hf : 0 ≤ f) (A : DigraphAlphabet G) :
    A.moment f ≤ capacity G f := le_csSup (momentSet_bddAbove G f hf) ⟨A,rfl⟩

theorem capacity_nonneg (f : ℝ) (hf : 0 ≤ f) : 0 ≤ capacity G f := by
  simpa only [empty_moment] using moment_le_capacity G f hf (DigraphAlphabet.empty G)

theorem capacity_le_card (f : ℝ) (hf : 0 ≤ f) : capacity G f ≤ (Fintype.card V : ℝ) := by
  apply csSup_le (momentSet_nonempty G f)
  rintro z ⟨A,rfl⟩
  exact A.moment_le_card f hf

/-- A graph with no vertices has zero moment capacity. -/
@[simp] theorem capacity_empty [IsEmpty V] (f : ℝ) (hf : 0 ≤ f) : capacity G f = 0 := by
  apply le_antisymm
  · simpa using capacity_le_card G f hf
  · exact capacity_nonneg G f hf

/-- Restriction to one H-fiber is an actual H-alphabet. -/
def fiber (C : DigraphAlphabet (lex G H)) (x : V) : DigraphAlphabet H where
  interval y := C.interval (x,y)
  ordered y z I J hI hJ hyz := C.ordered (x,y) (x,z) I J hI hJ (Or.inr ⟨rfl,hyz⟩)

/-- Every occupied fiber is replaced by its finite endpoint hull. -/
noncomputable def outer (C : DigraphAlphabet (lex G H)) : DigraphAlphabet G := by
  classical
  exact {
    interval := fun x => if hx : IntervalHull.occupied (fiber G H C x).interval then
      some (IntervalHull.hull (fiber G H C x).interval hx) else none
    ordered := by
      intro x y I J hI hJ hxy
      have hx : IntervalHull.occupied (fiber G H C x).interval := by
        by_contra hn
        simp only [dif_neg hn] at hI
        contradiction
      have hy : IntervalHull.occupied (fiber G H C y).interval := by
        by_contra hn
        simp only [dif_neg hn] at hJ
        contradiction
      have hi : IntervalHull.hull (fiber G H C x).interval hx = I := by
        simpa only [dif_pos hx, Option.some.injEq] using hI
      have hj : IntervalHull.hull (fiber G H C y).interval hy = J := by
        simpa only [dif_pos hy, Option.some.injEq] using hJ
      rw [← hi, ← hj]
      have h := IntervalHull.right_le_left (fiber G H C x).interval (fiber G H C y).interval
        (fun u v P Q hP hQ => C.ordered (x,u) (y,v) P Q hP hQ (Or.inl hxy))
      dsimp [IntervalHull.hull]
      linarith }

omit [Fintype V] in
@[simp] theorem outer_some (C : DigraphAlphabet (lex G H)) (x : V)
    (hx : IntervalHull.occupied (fiber G H C x).interval) :
    (outer G H C).interval x = some (IntervalHull.hull (fiber G H C x).interval hx) := by
  simp only [outer, dif_pos hx]

omit [Fintype V] in
@[simp] theorem outer_none (C : DigraphAlphabet (lex G H)) (x : V)
    (hx : ¬ IntervalHull.occupied (fiber G H C x).interval) :
    (outer G H C).interval x = none := by
  simp only [outer, dif_neg hx]

omit [Fintype V] in
theorem fiber_zero (C : DigraphAlphabet (lex G H)) (x : V)
    (hx : ¬ IntervalHull.occupied (fiber G H C x).interval) (f : ℝ) :
    (fiber G H C x).moment f = 0 := by
  unfold moment
  apply Finset.sum_eq_zero
  intro y _
  cases hy : (fiber G H C x).interval y with
  | none => rfl
  | some I => exact False.elim (hx ⟨y,I,hy⟩)

omit [Fintype V] in
/-- Each fiber costs at most its hull's f-moment times the H-capacity. -/
theorem fiber_moment_le (C : DigraphAlphabet (lex G H)) (x : V) (f : ℝ) (hf : 0 ≤ f) :
    (fiber G H C x).moment f ≤ weight f ((outer G H C).interval x) * capacity H f := by
  classical
  by_cases hx : IntervalHull.occupied (fiber G H C x).interval
  · let P := IntervalHull.hull (fiber G H C x).interval hx
    have hc := IntervalHull.hull_contains (fiber G H C x).interval hx
    rw [outer_some G H C x hx]
    change (fiber G H C x).moment f ≤ P.width ^ f * capacity H f
    rw [DigraphAlphabet.normalize_moment (fiber G H C x) P hc f]
    exact mul_le_mul_of_nonneg_left
      (moment_le_capacity H f hf (DigraphAlphabet.normalize (fiber G H C x) P hc))
      (Real.rpow_nonneg P.width_pos.le f)
  · rw [outer_none G H C x hx, fiber_zero G H C x hx f]
    simp only [weight, zero_mul, le_refl]

/-- The upper product bound is proved by concrete hulls, not by a recurrence. -/
theorem moment_lex_le (C : DigraphAlphabet (lex G H)) (f : ℝ) (hf : 0 ≤ f) :
    C.moment f ≤ capacity G f * capacity H f := by
  calc
    C.moment f = ∑ x : V, (fiber G H C x).moment f := by
      simp only [moment, fiber, Fintype.sum_prod_type]
    _ ≤ ∑ x : V, weight f ((outer G H C).interval x) * capacity H f :=
      Finset.sum_le_sum (fun x _ => fiber_moment_le G H C x f hf)
    _ = (outer G H C).moment f * capacity H f := by rw [← Finset.sum_mul]; rfl
    _ ≤ capacity G f * capacity H f :=
      mul_le_mul_of_nonneg_right (moment_le_capacity G f hf (outer G H C)) (capacity_nonneg H f hf)

theorem capacity_lex_le (f : ℝ) (hf : 0 ≤ f) :
    capacity (lex G H) f ≤ capacity G f * capacity H f := by
  apply csSup_le (momentSet_nonempty (lex G H) f)
  rintro z ⟨C,rfl⟩
  exact moment_lex_le G H C f hf

/-- Products of attained moments are attained by genuine nested alphabets. -/
theorem product_moment_le (f : ℝ) (hf : 0 ≤ f) (A : DigraphAlphabet G) (B : DigraphAlphabet H) :
    A.moment f * B.moment f ≤ capacity (lex G H) f := by
  rw [← DigraphAlphabet.product_moment A B f]
  exact moment_le_capacity (lex G H) f hf (DigraphAlphabet.product A B)

theorem le_capacity_lex (f : ℝ) (hf : 0 ≤ f) :
    capacity G f * capacity H f ≤ capacity (lex G H) f := by
  have hHnonneg := capacity_nonneg H f hf
  by_cases hH : capacity H f = 0
  · rw [hH,mul_zero]
    exact capacity_nonneg (lex G H) f hf
  have hHpos : 0 < capacity H f := lt_of_le_of_ne hHnonneg (Ne.symm hH)
  have hA : ∀ A : DigraphAlphabet G, A.moment f * capacity H f ≤ capacity (lex G H) f := by
    intro A
    by_cases hz : A.moment f = 0
    · rw [hz,zero_mul]
      exact capacity_nonneg (lex G H) f hf
    have hpos : 0 < A.moment f := lt_of_le_of_ne (A.moment_nonneg f) (Ne.symm hz)
    have hs : capacity H f ≤ capacity (lex G H) f / A.moment f := by
      apply csSup_le (momentSet_nonempty H f)
      rintro z ⟨B,rfl⟩
      apply (le_div_iff₀ hpos).mpr
      simpa only [mul_comm] using product_moment_le G H f hf A B
    simpa only [mul_comm] using (le_div_iff₀ hpos).mp hs
  apply (le_div_iff₀ hHpos).mp
  apply csSup_le (momentSet_nonempty G f)
  rintro z ⟨A,rfl⟩
  exact (le_div_iff₀ hHpos).mpr (hA A)

/-- Exact multiplicativity of interval-moment capacity for finite directed
lexicographic products, also valid at f=0. -/
theorem capacity_lex (f : ℝ) (hf : 0 ≤ f) :
    capacity (lex G H) f = capacity G f * capacity H f :=
  le_antisymm (capacity_lex_le G H f hf) (le_capacity_lex G H f hf)

/-- An edgeless graph selects every vertex with a full-width interval. -/
theorem capacity_edgeless (f : ℝ) (hf : 0 ≤ f) :
    capacity (fun _ _ : V => False) f = (Fintype.card V : ℝ) := by
  let A : DigraphAlphabet (fun _ _ : V => False) := {
    interval := fun _ => some UnitInterval.unit
    ordered := by intro x y I J hI hJ h; exact False.elim h }
  apply le_antisymm (capacity_le_card _ f hf)
  have h := moment_le_capacity (fun _ _ : V => False) f hf A
  simpa only [moment, A, weight, UnitInterval.unit, Real.one_rpow,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h

end NK.LexicographicCapacity
