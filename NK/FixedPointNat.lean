import Mathlib

/-! Outward rounding primitives for nonnegative fixed-point certificates.
These bounds concern exact natural arithmetic, including nonzero remainders. -/
namespace NK.FixedPointNat

/-- Integer ceiling of a nonnegative rational with positive denominator. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem floor_ratio_le (a b : ℕ) (hb : 0 < b) :
    ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / b := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (le_div_iff₀ hbR).mpr
  exact_mod_cast Nat.div_mul_le_self a b

theorem le_ceilDiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  have heq := Nat.div_add_mod (a+b-1) b
  have hmod := Nat.mod_lt (a+b-1) hb
  unfold ceilDiv
  rw [Nat.mul_comm b] at heq
  omega

theorem ratio_le_ceil (a b : ℕ) (hb : 0 < b) :
    (a : ℝ) / b ≤ (ceilDiv a b : ℝ) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  apply (div_le_iff₀ hbR).mpr
  exact_mod_cast le_ceilDiv_mul a b hb

/-- Floor/ceiling at scale S produce a sound real enclosure of a/b. -/
theorem enclose_ratio (a b S : ℕ) (hb : 0 < b) (hS : 0 < S) :
    (((a*S)/b : ℕ) : ℝ) / S ≤ (a : ℝ) / b ∧
    (a : ℝ) / b ≤ (ceilDiv (a*S) b : ℝ) / S := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  have hlo := floor_ratio_le (a*S) b hb
  have hhi := ratio_le_ceil (a*S) b hb
  constructor
  · apply (div_le_iff₀ hsR).mpr
    simpa only [Nat.cast_mul, mul_div_right_comm] using hlo
  · apply (le_div_iff₀ hsR).mpr
    simpa only [Nat.cast_mul, mul_div_right_comm] using hhi

/-- A nonnegative interval product can be rounded outwards at the same scale. -/
theorem enclose_mul (S lo₁ hi₁ lo₂ hi₂ : ℕ) (x y : ℝ) (hS : 0 < S)
    (hx : (lo₁ : ℝ)/S ≤ x ∧ x ≤ (hi₁ : ℝ)/S)
    (hy : (lo₂ : ℝ)/S ≤ y ∧ y ≤ (hi₂ : ℝ)/S) :
    (((lo₁*lo₂)/S : ℕ) : ℝ)/S ≤ x*y ∧
    x*y ≤ (ceilDiv (hi₁*hi₂) S : ℝ)/S := by
  have hsR : (0 : ℝ) < S := by exact_mod_cast hS
  have hx0 : 0 ≤ x := (by positivity : (0 : ℝ) ≤ (lo₁ : ℝ)/S).trans hx.1
  have hy0 : 0 ≤ y := (by positivity : (0 : ℝ) ≤ (lo₂ : ℝ)/S).trans hy.1
  have hlo := div_le_div_of_nonneg_right (floor_ratio_le (lo₁*lo₂) S hS) hsR.le
  have hhi := div_le_div_of_nonneg_right (ratio_le_ceil (hi₁*hi₂) S hS) hsR.le
  constructor
  · apply hlo.trans
    simpa only [Nat.cast_mul, div_div, div_mul_div_comm] using
      mul_le_mul hx.1 hy.1 (by positivity : (0 : ℝ) ≤ (lo₂ : ℝ)/S) hx0
  · apply le_trans _ hhi
    simpa only [Nat.cast_mul, div_div, div_mul_div_comm] using
      mul_le_mul hx.2 hy.2 hy0 (by positivity : (0 : ℝ) ≤ (hi₁ : ℝ)/S)

end NK.FixedPointNat
