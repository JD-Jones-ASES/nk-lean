import NK.PrimeBlockCapacity

#print axioms NK.powerArc_of_first_block
#print axioms NK.powerArc_iff_firstDifference_block
#print axioms NK.blockWordEquiv
#print axioms NK.powerArc_iff_blockWord
#print axioms NK.binary_square_block_graph_counterexample
#print axioms NK.prime_power_capacity
#print axioms NK.prime_power_moment_le
#print axioms NK.IntervalAlphabet.toPowerDigraph_moment
#print axioms NK.IntervalAlphabet.moment_le_prime_power_capacity

-- Literal low-to-high orientation: 123 = 6 + 9*4 + 81*1.
example : (NK.blockWordEquiv 9 3 (by decide) ⟨123, by decide⟩ ⟨0, by decide⟩).val = 6 := rfl
example : (NK.blockWordEquiv 9 3 (by decide) ⟨123, by decide⟩ ⟨1, by decide⟩).val = 4 := rfl
example : (NK.blockWordEquiv 9 3 (by decide) ⟨123, by decide⟩ ⟨2, by decide⟩).val = 1 := rfl

-- A unit square root is lifted beyond the local block.
example : NK.PowerArc 2 (9 ^ 2) 0 10 := by
  apply NK.powerArc_of_first_block 3 2 2 0 10 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · intro i hi; omega
  · exact ⟨by decide, 1, by decide⟩

-- Nonunit differences: the common lower block must be factored out.
example : NK.PowerArc 3 (27 ^ 2) 0 27 := by
  apply NK.powerArc_of_first_block 3 3 2 0 27 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · intro i hi
    have : i = 0 := by omega
    subst i
    decide
  · exact ⟨by decide, 1, by decide⟩
example : NK.PowerArc 4 (16 ^ 2) 0 16 := by
  apply NK.powerArc_of_first_block 2 4 2 0 16 1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  · intro i hi
    have : i = 0 := by omega
    subst i
    decide
  · exact ⟨by decide, 1, by decide⟩

example : NK.FirstDifferencePowerArc 2 4 (NK.fullBlockDigits 2 2 2 0)
    (NK.fullBlockDigits 2 2 2 5) ∧ ¬ NK.PowerArc 2 16 0 5 :=
  NK.binary_square_block_graph_counterexample

-- Ordinary capacity specializations, with all interval supports allowed.
example (f : ℝ) (hf : 0 ≤ f) : NK.modularCapacity 2 81 f = (NK.modularCapacity 2 9 f)^2 :=
  NK.prime_power_capacity 3 2 2 (by decide) (by decide) (by decide) (by decide) f hf
example (f : ℝ) (hf : 0 ≤ f) : NK.modularCapacity 3 729 f = (NK.modularCapacity 3 27 f)^2 :=
  NK.prime_power_capacity 3 3 2 (by decide) (by decide) (by decide) (by decide) f hf
example (f : ℝ) (hf : 0 ≤ f) : NK.modularCapacity 4 256 f = (NK.modularCapacity 4 16 f)^2 :=
  NK.prime_power_capacity 2 4 2 (by decide) (by decide) (by decide) (by decide) f hf
example (f : ℝ) (hf : 0 ≤ f) : NK.modularCapacity 1 8 f = (NK.modularCapacity 1 2 f)^3 :=
  NK.prime_power_capacity 2 1 3 (by decide) (by decide) (by decide) (by decide) f hf

example (A : NK.IntervalAlphabet 2 81) (f : ℝ) (hf : 0 ≤ f) :
    A.moment f ≤ (NK.modularCapacity 2 9 f)^2 :=
  NK.IntervalAlphabet.moment_le_prime_power_capacity 3 2 2
    (by decide) (by decide) (by decide) (by decide) f hf A
