import NK.BinaryDepth

/-! The depth is exactly10^15. Choice keeps it propositionally, but not
definitionally, equal to the numeral so independent kernels cannot expand
the enormous natural powers while checking definitional equalities. -/
namespace NK.Certificates
open NK.RationalPowerBounds

theorem binaryDepth_exists : ∃ n : ℕ, n = 1000000000000000 := ⟨1000000000000000, rfl⟩

noncomputable def binaryDepth : ℕ := Classical.choose binaryDepth_exists

theorem binaryDepth_eq : binaryDepth = 1000000000000000 :=
  Classical.choose_spec binaryDepth_exists

theorem binaryDepth_ge_one : 1 ≤ binaryDepth := by
  rw [binaryDepth_eq]
  decide

theorem binaryDepth_pos : 0 < binaryDepth :=
  lt_of_lt_of_le Nat.zero_lt_one binaryDepth_ge_one

theorem binary_depth_log : (1 + (75806770413 / 100000000000 : ℝ) * (1000000000000000 : ℝ)) * Real.log 4 +
    (15494199041779 / 100000000000000 : ℝ) * Real.log 2 ≤ ((1000000000000000 : ℝ) - 1) * Real.log (1430119207986461 / 500000000000000 : ℝ) := by
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

theorem binary_depth_moment : (((4 ^ binaryDepth : ℕ):ℝ)^(75806770413 / 100000000000 : ℝ)) ≤
    (1/2:ℝ)^(15494199041779 / 100000000000000 : ℝ) * (1/4:ℝ) * (1430119207986461 / 500000000000000 : ℝ)^(binaryDepth - 1) := by
  apply binary_depth_moment_of_logs binaryDepth (75806770413 / 100000000000 : ℝ) (15494199041779 / 100000000000000 : ℝ) (1430119207986461 / 500000000000000 : ℝ)
    binaryDepth_ge_one (by norm_num)
  simpa only [binaryDepth_eq, Nat.cast_ofNat] using binary_depth_log

end NK.Certificates
