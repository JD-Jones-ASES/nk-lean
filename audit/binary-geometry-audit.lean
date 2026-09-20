import NK.Certificates.BinaryGeometry

open NK NK.BinaryPolicy NK.Certificates

#print axioms binaryRows_valid
#print axioms binarySeeds
#print axioms binaryPolicy

example (i : Fin 25) : (1 / 4 : ℝ) ≤ (binarySeeds i).interval.width := (binarySeeds i).quarter

-- The unrestricted root has both full windows.
example (p : Fin 2) : binaryWindows 1 p = some UnitInterval.unit := by
  fin_cases p <;> norm_num [binaryWindows, binaryState1, UnitInterval.unit]

-- These absent classes are essential to the original root row.
example : binaryClass1 4 = none ∧ binaryClass1 7 = none := by constructor <;> rfl

-- A 10^(-8) left shift of root class1 would violate the actual class0→class1 edge.
example : ∃ I J : UnitInterval, binaryClass1 0 = some I ∧ binaryClass1 1 = some J ∧
    ¬ (I.left + I.width ≤ J.left - 1 / (10 : ℝ) ^ 8) := by
  norm_num [binaryClass1]
