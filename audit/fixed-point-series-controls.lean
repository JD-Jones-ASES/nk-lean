import NK.FixedPointSeries

open NK.FixedPointSeries

#print axioms taylorState_sound
#print axioms oddState_sound
#print axioms expBounds_sound
#print axioms logBounds_sound

example : taylor 100 1 8 3 = ⟨112, 114⟩ := by decide
example : taylor 1000 1 8 5 = ⟨1132, 1135⟩ := by decide
example : taylor 1000 0 8 5 = ⟨1000, 1000⟩ := by decide
example : atanhSum 100 1 3 3 = ⟨68, 74⟩ := by decide
example : atanhSum 1000 1 3 5 = ⟨690, 700⟩ := by decide
example : atanhSum 1000 0 2 5 = ⟨0, 0⟩ := by decide

example : expBounds (10 ^ 15) 1 8 = ⟨1133148453066823, 1133148453066852⟩ := by decide
example : logBounds (10 ^ 15) 2 1 = ⟨693147180559930, 693147180560011⟩ := by decide

-- The same kernel reduction remains practical at the certificate's 50-digit scale.
example : expBounds (10 ^ 50) 1 8 =
    ⟨113314845306682631682900722781179387256550313174506,
     113314845306682631682900722781179387256550313174535⟩ := by decide
example : logBounds (10 ^ 50) 2 1 =
    ⟨69314718055994530941723212145817656807543767846584,
     69314718055994530941723212145817656808543767846664⟩ := by decide

example : (1133148453066823 : ℝ) / 10 ^ 15 ≤ Real.exp (1 / 8) ∧
    Real.exp (1 / 8) ≤ (1133148453066852 : ℝ) / 10 ^ 15 := by
  have h := expBounds_sound (10 ^ 15) 1 8 (by norm_num) (by decide) (by decide)
  have hv : expBounds (10 ^ 15) 1 8 = ⟨1133148453066823, 1133148453066852⟩ := by decide
  rw [hv] at h
  norm_num [Encloses] at h ⊢
  exact h

example : (693147180559930 : ℝ) / 10 ^ 15 ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180560011 : ℝ) / 10 ^ 15 := by
  have h := logBounds_sound (10 ^ 15) 2 1 (by norm_num) (by decide) (by decide) (by decide)
  have hv : logBounds (10 ^ 15) 2 1 = ⟨693147180559930, 693147180560011⟩ := by decide
  rw [hv] at h
  norm_num [Encloses] at h ⊢
  exact h

-- Dividing a nonintegral term must round its upper endpoint upwards.
example : scaleRatio ⟨100, 100⟩ 1 8 = ⟨12, 13⟩ := by decide
example : ¬ Encloses 100 ⟨12, 12⟩ (1 / 8) := by norm_num [Encloses]

-- The empty finite series and exact-zero log input have the right values.
example : taylor 100 1 8 0 = ⟨0, 0⟩ := by decide
example : atanhSum 100 1 3 0 = ⟨0, 0⟩ := by decide

-- Invalid logarithm and exponential reduction domains are rejected.
example : ¬ (3 ≤ 2 * (1 : ℕ)) := by decide
example : ¬ (8 * 2 ≤ (8 : ℕ)) := by decide
