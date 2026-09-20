import Mathlib

/-! # Analytic soundness bounds for rational numerical certificates

These are finite-sum real inequalities. At rational inputs every displayed
sum and error bound is rational, so subsequent certificates can check them
using exact arithmetic. No native evaluation axiom is used.

The exponential bound uses a positive Taylor tail. The logarithm bound
is Mathlib's atanh remainder estimate, without the sharper factor
`1/(2*n+1)`. That sharper tail and fixed-point rounding operations
are outside the scope of this module.
-/

namespace NK.NumericBounds

/-- The first n terms of the exponential Taylor series. -/
noncomputable def expTaylor (x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, x ^ j / j.factorial

/-- Positive Taylor sums bound exp from below; the tail is at most twice
the first omitted term on [0,1]. -/
theorem expTaylor_bounds (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    expTaylor x n ≤ Real.exp x ∧
      Real.exp x ≤ expTaylor x n + 2 * x ^ n / n.factorial := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf0 : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hratio : x ^ n * ((n : ℝ) + 1) / (n.factorial * n) ≤
      2 * x ^ n / n.factorial := by
    calc
      x ^ n * ((n : ℝ) + 1) / (n.factorial * n) ≤
          x ^ n * (2 * (n : ℝ)) / (n.factorial * n) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg hf0.le hn0.le)
        exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hx n)
      _ = 2 * x ^ n / n.factorial := by field_simp
  exact ⟨Real.sum_le_exp_of_nonneg hx n,
    (Real.exp_bound' hx hx1 (by omega : 0 < n)).trans (add_le_add le_rfl hratio)⟩

/-- The exact uniform tail used after range reduction to [0,1/8].
For a sum through degree 30, use n = 31. -/
theorem expTaylor_eighth_bounds (x : ℝ) (hx : 0 ≤ x) (hx8 : x ≤ 1 / 8)
    (n : ℕ) (hn : 1 ≤ n) :
    expTaylor x n ≤ Real.exp x ∧
      Real.exp x ≤ expTaylor x n + 2 / ((8 : ℝ) ^ n * n.factorial) := by
  have h := expTaylor_bounds x hx (by linarith) n hn
  refine ⟨h.1, h.2.trans (add_le_add le_rfl ?_)⟩
  calc
    2 * x ^ n / n.factorial ≤ 2 * (1 / 8 : ℝ) ^ n / n.factorial := by
      gcongr
    _ = 2 / ((8 : ℝ) ^ n * n.factorial) := by
      simp [div_eq_mul_inv, mul_left_comm, mul_comm]

/-- Thirty-one terms on [0,1/8] have analytic truncation error below 10^(-60).
This does not include any rounding error in a fixed-point implementation. -/
theorem expTaylor_eighth_bounds_thirtyone (x : ℝ) (hx : 0 ≤ x) (hx8 : x ≤ 1 / 8) :
    expTaylor x 31 ≤ Real.exp x ∧
      Real.exp x ≤ expTaylor x 31 + 1 / (10 : ℝ) ^ 60 := by
  have h := expTaylor_eighth_bounds x hx hx8 31 (by decide)
  exact ⟨h.1, h.2.trans (add_le_add le_rfl (by norm_num))⟩

/-- The first n odd terms in the atanh expansion of a logarithm. -/
noncomputable def atanhLogSum (z : ℝ) (n : ℕ) : ℝ :=
  2 * ∑ j ∈ Finset.range n, z ^ (2 * j + 1) / (2 * j + 1)

/-- A finite rational lower bound and a rational upper remainder for
log((1+z)/(1-z)), from Mathlib's existing logarithm remainder theorem. -/
theorem atanhLog_bounds (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (n : ℕ) :
    atanhLogSum z n ≤ Real.log ((1 + z) / (1 - z)) ∧
      Real.log ((1 + z) / (1 - z)) ≤
        atanhLogSum z n + 2 * z ^ (2 * n + 1) / (1 - z ^ 2) := by
  have hlo := Real.sum_range_le_log_div hz hz1 n
  have hhi := Real.log_div_le_sum_range_add hz hz1 n
  dsimp [atanhLogSum]
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

/-- On the reduced domain [1,2], z=(u-1)/(u+1) is in [0,1/3],
giving a uniform rational remainder. -/
theorem log_unit_bounds (u : ℝ) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) (n : ℕ) :
    atanhLogSum ((u - 1) / (u + 1)) n ≤ Real.log u ∧
      Real.log u ≤ atanhLogSum ((u - 1) / (u + 1)) n +
        (9 / 4 : ℝ) * (1 / 3 : ℝ) ^ (2 * n + 1) := by
  let z : ℝ := (u - 1) / (u + 1)
  have hupos : 0 < u + 1 := by linarith
  have hz : 0 ≤ z := div_nonneg (by linarith) hupos.le
  have hz3 : z ≤ 1 / 3 := by
    apply (div_le_iff₀ hupos).mpr
    linarith
  have hz1 : z < 1 := by linarith
  have hrecover : (1 + z) / (1 - z) = u := by
    apply (div_eq_iff (by linarith : 1 - z ≠ 0)).mpr
    dsimp [z]
    field_simp
    ring
  have h := atanhLog_bounds z hz hz1 n
  rw [hrecover] at h
  refine ⟨h.1, h.2.trans (add_le_add le_rfl ?_)⟩
  have hden : (8 / 9 : ℝ) ≤ 1 - z ^ 2 := by
    have hsq := pow_le_pow_left₀ hz hz3 2
    norm_num at hsq
    linarith
  have hnum : 2 * z ^ (2 * n + 1) ≤ 2 * (1 / 3 : ℝ) ^ (2 * n + 1) :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hz3 _) (by norm_num)
  calc
    2 * z ^ (2 * n + 1) / (1 - z ^ 2) ≤
        2 * (1 / 3 : ℝ) ^ (2 * n + 1) / (8 / 9) :=
      div_le_div₀ (by positivity) hnum (by norm_num) hden
    _ = (9 / 4 : ℝ) * (1 / 3 : ℝ) ^ (2 * n + 1) := by ring

/-- Sixteen odd terms already give a uniform error below 10^(-12) on [1,2]. -/
theorem log_unit_bounds_sixteen (u : ℝ) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    atanhLogSum ((u - 1) / (u + 1)) 16 ≤ Real.log u ∧
      Real.log u ≤ atanhLogSum ((u - 1) / (u + 1)) 16 + 1 / (10 : ℝ) ^ 12 := by
  have h := log_unit_bounds u hu1 hu2 16
  exact ⟨h.1, h.2.trans (add_le_add le_rfl (by norm_num))⟩

/-- Forty odd terms give error below 10^(-38), even with the weaker
Mathlib remainder used here. No fixed-point rounding error is included. -/
theorem log_unit_bounds_forty (u : ℝ) (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    atanhLogSum ((u - 1) / (u + 1)) 40 ≤ Real.log u ∧
      Real.log u ≤ atanhLogSum ((u - 1) / (u + 1)) 40 + 1 / (10 : ℝ) ^ 38 := by
  have h := log_unit_bounds u hu1 hu2 40
  exact ⟨h.1, h.2.trans (add_le_add le_rfl (by norm_num))⟩

/-- Logarithm and exponential enclosures compose into an rpow enclosure.
The exponent is nonnegative, so the endpoint order is preserved. -/
theorem rpow_bounds_of_log_bounds (x f l u L U : ℝ)
    (hx : 0 < x) (hf : 0 ≤ f) (hl : l ≤ Real.log x) (hu : Real.log x ≤ u)
    (hL : L ≤ Real.exp (f * l)) (hU : Real.exp (f * u) ≤ U) :
    L ≤ x ^ f ∧ x ^ f ≤ U := by
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x) f]
  exact ⟨hL.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hl hf)),
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hf)).trans hU⟩

end NK.NumericBounds
