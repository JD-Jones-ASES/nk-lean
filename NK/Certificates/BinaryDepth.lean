import NK.BinaryDepth

/-! Finite depth10^15, certified without expanding4^(10^15). -/
namespace NK.Certificates
open NK.RationalPowerBounds

theorem binary_depth_moment : (((4 ^ 1000000000000000 : ℕ):ℝ)^(75806770413 / 100000000000 : ℝ)) ≤
    (1/2:ℝ)^(15494199041779 / 100000000000000 : ℝ) * (1/4:ℝ) * (1430119207986461 / 500000000000000 : ℝ)^(1000000000000000-1 : ℕ) := by
  apply binary_depth_moment_of_logs 1000000000000000 (75806770413 / 100000000000 : ℝ) (15494199041779 / 100000000000000 : ℝ) (1430119207986461 / 500000000000000 : ℝ) (by decide) (by norm_num)
  have ha := (logPosBounds_sound 1000000000000000000000000 1430119207986461 500000000000000 1 (by decide) (by decide) (by decide) (by decide)).1
  have hav : (logPosBounds 1000000000000000000000000 1430119207986461 500000000000000 1).lo = 1050904983585618163878102 := by decide
  rw [hav] at ha
  have hb := (logPosBounds_sound 1000000000000000000000000 4 1 2 (by decide) (by decide) (by decide) (by decide)).2
  have hbv : (logPosBounds 1000000000000000000000000 4 1 2).hi = 1386294361119890618834583 := by decide
  rw [hbv] at hb
  have hc := (logPosBounds_sound 1000000000000000000000000 2 1 1 (by decide) (by decide) (by decide) (by decide)).2
  have hcv : (logPosBounds 1000000000000000000000000 2 1 1).hi = 693147180559945309417292 := by decide
  rw [hcv] at hc
  have haW := mul_le_mul_of_nonneg_left ha (by norm_num : (0:ℝ) ≤ (1000000000000000:ℝ)-1)
  have hbW := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1+(75806770413 / 100000000000 : ℝ)*1000000000000000)
  have hcW := mul_le_mul_of_nonneg_left hc (by norm_num : (0:ℝ) ≤ (15494199041779 / 100000000000000 : ℝ))
  norm_num at haW hbW hcW ⊢
  linarith

end NK.Certificates
