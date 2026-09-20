import NK.NumericReduction

open NK.NumericReduction NK.NumericBounds

#print axioms exists_log_dyadic_rat
#print axioms log_dyadic_bounds
#print axioms exists_exp_dyadic_rat
#print axioms exp_dyadic_bounds
#print axioms exp_neg_dyadic_bounds

example : shiftLower (-3) (2 / 3) (7 / 10) = -(21 / 10 : ℝ) := by
  norm_num [shiftLower]

example : shiftUpper (-3) (2 / 3) (7 / 10) = (-2 : ℝ) := by
  norm_num [shiftUpper]

example : shiftLower 0 (-100) 100 = 0 ∧ shiftUpper 0 (-100) 100 = 0 := by
  norm_num [shiftLower, shiftUpper]

example : Real.log (3 / 16 : ℝ) = -3 * Real.log 2 + Real.log (3 / 2 : ℝ) := by
  have h := log_rat_dyadic (3 / 16) (3 / 2) (-3) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example (l h : ℝ) (hl : l ≤ Real.log (3 / 2)) (hh : Real.log (3 / 2) ≤ h) :
    -h ≤ Real.log (2 / 3 : ℝ) ∧ Real.log (2 / 3 : ℝ) ≤ -l := by
  simpa using log_inv_bounds (3 / 2) l h hl hh

example (u l h : ℝ) (hl0 : 0 ≤ l) (hl : l ≤ Real.exp u) (hh : Real.exp u ≤ h) :
    l ≤ Real.exp u ∧ Real.exp u ≤ h := by
  simpa using exp_dyadic_bounds u l h 0 hl0 hl hh

example (m : ℕ) : Real.exp ((2 : ℝ) ^ m * 0) = 1 := by simp

private theorem exp_eighth_coarse :
    (1 : ℝ) ≤ Real.exp (1 / 8) ∧ Real.exp (1 / 8) ≤ 2 := by
  have h := expTaylor_eighth_bounds (1 / 8) (by norm_num) (by norm_num) 1 (by decide)
  norm_num [expTaylor] at h
  exact ⟨Real.one_le_exp_iff.mpr (by norm_num), h.trans (by norm_num)⟩

example : (1 : ℝ) ≤ Real.exp 1 ∧ Real.exp 1 ≤ 256 := by
  have h := exp_dyadic_bounds (1 / 8) 1 2 3 (by norm_num)
    exp_eighth_coarse.1 exp_eighth_coarse.2
  norm_num at h ⊢
  exact h

example : (1 / 256 : ℝ) ≤ Real.exp (-1) ∧ Real.exp (-1) ≤ 1 := by
  have h := exp_neg_dyadic_bounds (1 / 8) 1 2 3 (by norm_num)
    exp_eighth_coarse.1 exp_eighth_coarse.2
  norm_num at h ⊢
  exact h

-- Wrong negative-shift endpoint selection fails even on rational data.
example : ¬ ((-3 : ℝ) * (2 / 3) ≤ (-3 : ℝ) * (7 / 10)) := by norm_num

-- A negative lower endpoint cannot be propagated through an even power.
example : (-2 : ℝ) ≤ Real.exp 0 ∧ ¬ ((-2 : ℝ) ^ 2 ≤ Real.exp 0) := by norm_num

-- Reciprocal intervals must reverse their endpoints.
example : ¬ ((1 : ℝ) / 1 ≤ (1 : ℝ) / 2) := by norm_num
