import Mathlib

/-! Multiplying the component stopping estimates charges a single global
rank height and one polynomial pigeonhole factor. -/
namespace NK

/-- Multiply local cardinality estimates, adding their moment exponents. -/
theorem list_moment_product {ι : Type*} (l : List ι) (x y f : ι → ℝ) (c δ : ℝ)
    (hc : 0 ≤ c) (hδ : 0 < δ)
    (hx : ∀ i ∈ l, 0 ≤ x i) (hy : ∀ i ∈ l, 0 ≤ y i)
    (hlocal : ∀ i ∈ l, x i ≤ c * y i * δ ^ f i) :
    (l.map x).prod ≤ c ^ l.length * (l.map y).prod * δ ^ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons i is ih =>
    have hx0 := hx i List.mem_cons_self
    have hy0 := hy i List.mem_cons_self
    have hloc := hlocal i List.mem_cons_self
    have ih' := ih (fun i hi => hx i (List.mem_cons_of_mem _ hi))
      (fun i hi => hy i (List.mem_cons_of_mem _ hi))
      (fun i hi => hlocal i (List.mem_cons_of_mem _ hi))
    have hprod : 0 ≤ (is.map x).prod := List.prod_nonneg (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact hx i (List.mem_cons_of_mem _ hi))
    have hmul := mul_le_mul hloc ih' hprod
      (mul_nonneg (mul_nonneg hc hy0) (Real.rpow_nonneg hδ.le _))
    simp only [List.map_cons, List.prod_cons, List.sum_cons, List.length_cons,
      pow_succ, Real.rpow_add hδ]
    calc
      _ ≤ _ := hmul
      _ = _ := by ring

/-- Real powers commute with finite nonnegative products. -/
theorem list_prod_rpow {ι : Type*} (l : List ι) (x : ι → ℝ) (α : ℝ)
    (hx : ∀ i ∈ l, 0 ≤ x i) :
    (l.map x).prod ^ α = (l.map (fun i => x i ^ α)).prod := by
  induction l with
  | nil => simp
  | cons i is ih =>
    have hprod : 0 ≤ (is.map x).prod := List.prod_nonneg (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact hx i (List.mem_cons_of_mem _ hi))
    simp only [List.map_cons, List.prod_cons,
      Real.mul_rpow (hx i List.mem_cons_self) hprod,
      ih (fun i hi => hx i (List.mem_cons_of_mem _ hi))]

/-- Pay the shared rank height out of the strict surplus budget. -/
theorem absorb_rank_cost (M Q h c δ F α : ℝ) (n : ℕ)
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hh : 0 ≤ h)
    (hcounts : M ^ α ≤ c ^ n * Q * δ ^ F)
    (hbudget : h ^ α * c ^ n * δ ^ F ≤ 1) :
    (M * h) ^ α ≤ Q := by
  rw [Real.mul_rpow hM hh]
  have h1 := mul_le_mul_of_nonneg_right hcounts (Real.rpow_nonneg hh α)
  have h2 := mul_le_mul_of_nonneg_left hbudget hQ
  nlinarith

end NK
