import Mathlib

/-! A strict moment surplus defeats the common rank-height cost and the
finite stopping-layer pigeonhole loss. This module supplies the elementary
polynomial-times-geometric limit with an explicit existential interface. -/
namespace NK
open Filter
open scoped Topology

/-- Every fixed polynomial loss is eventually dominated by geometric decay. -/
theorem exists_polynomial_geometric_small (C r : ℝ) (n K₀ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) :
    ∃ K : ℕ, K₀ ≤ K ∧ C * ((K : ℝ) + 1) ^ n * r ^ K < 1 := by
  have hlim := tendsto_pow_const_mul_const_pow_of_lt_one n hr.le hr1
  have hshift : Tendsto (fun K : ℕ => K + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have h := (hlim.comp hshift).const_mul (C / r)
  have heq : (fun K : ℕ => C / r * (((K + 1 : ℕ) : ℝ) ^ n * r ^ (K+1))) =
      (fun K : ℕ => C * ((K : ℝ)+1)^n * r^K) := by
    funext K
    push_cast
    rw [pow_succ]
    field_simp
  change Tendsto (fun K : ℕ => C / r * (((K + 1 : ℕ) : ℝ) ^ n * r ^ (K+1))) atTop (𝓝 (C/r*0)) at h
  rw [heq] at h
  simp only [mul_zero] at h
  have hsmall := h.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)
  exact ((eventually_ge_atTop K₀).and hsmall).exists

/-- The exponent F−α is precisely the strict surplus in the moment criterion. -/
theorem exists_moment_surplus_scale (C ρ F α : ℝ) (n K₀ : ℕ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hF : α < F) :
    ∃ K : ℕ, K₀ ≤ K ∧ C * ((K : ℝ) + 1)^n * (ρ ^ K) ^ (F-α) < 1 := by
  have hr : 0 < ρ ^ (F-α) := Real.rpow_pos_of_pos hρ _
  have hr1 : ρ ^ (F-α) < 1 := Real.rpow_lt_one hρ.le hρ1 (sub_pos.mpr hF)
  obtain ⟨K, hK, hsmall⟩ := exists_polynomial_geometric_small C (ρ ^ (F-α)) n K₀ hr hr1
  refine ⟨K, hK, ?_⟩
  rwa [← Real.rpow_pow_comm hρ.le (F-α) K]

end NK
