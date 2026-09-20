import NK.RationalPowerBounds

open NK.FixedPointSeries NK.RationalPowerBounds

#print axioms logPosBounds_sound
#print axioms expPosBounds_sound
#print axioms rpowBounds_sound
#print axioms reciprocal_sound
#print axioms unitRpowBounds_sound

example : logPosBounds (10 ^ 24) 17 3 2 =
    ⟨1734601055388106388854228, 1734601055388106388854471⟩ := by decide
example : expPosBounds (10 ^ 24) 3 2 4 =
    ⟨4481689070338064822601624, 4481689070338064822603467⟩ := by decide
example : rpowBounds (10 ^ 24) 2 1 1 2 1 2 =
    ⟨1414213562373095048801643, 1414213562373095048801868⟩ := by decide
example : unitRpowBounds (10 ^ 24) 2 1 1 2 1 2 =
    ⟨707106781186547524400754, 707106781186547524400868⟩ := by decide

example : Encloses (10 ^ 24)
    ⟨1414213562373095048801643, 1414213562373095048801868⟩
    ((2 : ℝ) ^ (1 / 2 : ℝ)) := by
  have h := rpowBounds_sound (10 ^ 24) 2 1 1 2 1 2
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv : rpowBounds (10 ^ 24) 2 1 1 2 1 2 =
      ⟨1414213562373095048801643, 1414213562373095048801868⟩ := by decide
  rw [hv] at h
  simpa using h

example : Encloses (10 ^ 24)
    ⟨707106781186547524400754, 707106781186547524400868⟩
    ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) := by
  have h := unitRpowBounds_sound (10 ^ 24) 2 1 1 2 1 2
    (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv : unitRpowBounds (10 ^ 24) 2 1 1 2 1 2 =
      ⟨707106781186547524400754, 707106781186547524400868⟩ := by decide
  rw [hv] at h
  simpa using h

-- Endpoints: exponent zero and a unit base remain valid enclosures.
example : rpowBounds (10 ^ 24) 5 2 0 1 1 0 =
    ⟨1000000000000000000000000, 1000000000000000000000001⟩ := by decide
example : unitRpowBounds (10 ^ 24) 1 1 1 2 0 0 =
    ⟨999999999999999999999969, 1000000000000000000000000⟩ := by decide

-- Too small an exponential reduction depth fails its explicit guard.
example : ¬ (8 * (powerLogBounds (10 ^ 24) 2 1 1 2 1).hi ≤ 10 ^ 24 * 2 ^ 0) := by decide
-- Too large a logarithm shift fails its lower reduction condition.
example : ¬ (3 * 2 ^ 3 ≤ (17 : ℕ)) := by decide

-- Dropping the positive lower-endpoint guard would make inversion unsound.
example : Encloses 1 ⟨0, 1⟩ (1 / 2) := by norm_num [Encloses]
example : ¬ Encloses 1 (reciprocal 1 ⟨0, 1⟩) (2 : ℝ) := by
  norm_num [Encloses, reciprocal, NK.FixedPointNat.ceilDiv]
