import NK.RationalPowerBounds

/-! Logarithmic finite-depth certificate, avoiding evaluation of the enormous
integer modulus. The conclusion concerns an actual, finite perfect-square base. -/
namespace NK

theorem binary_depth_moment_of_logs (m : ℕ) (α f a : ℝ)
    (hm : 1 ≤ m) (ha : 0 < a)
    (hlog : (1 + α*m) * Real.log 4 + f*Real.log 2 ≤ ((m:ℝ)-1)*Real.log a) :
    (((4 ^ m : ℕ):ℝ)^α) ≤ (1/2:ℝ)^f * (1/4:ℝ) * a^(m-1) := by
  have hL : (0:ℝ) < (((4 ^ m : ℕ):ℝ)^α) := by positivity
  have hR : (0:ℝ) < (1/2:ℝ)^f * (1/4:ℝ) * a^(m-1) := by positivity
  apply (Real.log_le_log_iff hL hR).mp
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_rpow (by positivity), Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num), Real.log_pow]
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hquarter : Real.log (1/4:ℝ) = -Real.log 4 := by rw [one_div, Real.log_inv]
  rw [hhalf, hquarter, Nat.cast_sub hm, Nat.cast_one]
  nlinarith [hlog]

end NK
