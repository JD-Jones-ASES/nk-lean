import NK.FixedPointNat

example : NK.FixedPointNat.ceilDiv 10 3 = 4 := by decide
example : NK.FixedPointNat.ceilDiv 0 7 = 0 := by decide
example : NK.FixedPointNat.ceilDiv 21 7 = 3 := by decide
example : ((10 / 3 : ℕ) : ℝ) / 10 ≤ 1/3 ∧
    (1/3 : ℝ) ≤ (NK.FixedPointNat.ceilDiv 10 3 : ℝ) / 10 := by
  simpa using NK.FixedPointNat.enclose_ratio 1 3 10 (by decide) (by decide)
example : ¬ ((1/3 : ℝ) ≤ ((10/3 : ℕ) : ℝ)/10) := by norm_num
#print axioms NK.FixedPointNat.enclose_ratio
#print axioms NK.FixedPointNat.enclose_mul
