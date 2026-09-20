import NK.NumericBounds

open NK.NumericBounds

#print axioms NK.NumericBounds.expTaylor_eighth_bounds
#print axioms NK.NumericBounds.log_unit_bounds
#print axioms NK.NumericBounds.log_unit_bounds_forty
#print axioms NK.NumericBounds.rpow_bounds_of_log_bounds

example : (693147180559 : ℝ) / 10^12 < Real.log 2 ∧
    Real.log 2 < (693147180561 : ℝ) / 10^12 := by
  have h := log_unit_bounds_sixteen 2 (by norm_num) (by norm_num)
  constructor
  · refine lt_of_lt_of_le ?_ h.1
    norm_num [atanhLogSum, Finset.sum_range_succ]
  · refine lt_of_le_of_lt h.2 ?_
    norm_num [atanhLogSum, Finset.sum_range_succ]

example : (1133148453066 : ℝ) / 10^12 < Real.exp (1/8) ∧
    Real.exp (1/8) < (1133148453067 : ℝ) / 10^12 := by
  have h := expTaylor_eighth_bounds_thirtyone (1/8) (by norm_num) le_rfl
  constructor
  · refine lt_of_lt_of_le ?_ h.1
    norm_num [expTaylor, Finset.sum_range_succ]
  · refine lt_of_le_of_lt h.2 ?_
    norm_num [expTaylor, Finset.sum_range_succ]

-- The reduced endpoints zero and one include exact exp(0) and log(1).
example : expTaylor 0 31 = Real.exp 0 := by
  norm_num [expTaylor, Finset.sum_range_succ]
example : atanhLogSum 0 40 = Real.log 1 := by
  norm_num [atanhLogSum]

-- Discarding the tail gives a false upper bound already at degree zero.
example : ¬ Real.exp (1/8) ≤ expTaylor (1/8) 1 := by
  norm_num [expTaylor, Finset.sum_range_succ]
