import NK.RankedTransfer

#print axioms NK.geometric_witnesses_allN
#print axioms NK.powerLowerBound_of_geometric_witnesses
#print axioms NK.rankedBlock_geometric_witnesses
#print axioms NK.powerLowerBound_of_rankedBlock

-- The L=0 / N=1 endpoint and Q=1 are part of the all-N theorem.
example : NK.PowerLowerBound 2 0 := by
  apply NK.powerLowerBound_of_geometric_witnesses 2 4 1 (by decide) (by decide)
    0 (by norm_num) (by norm_num)
  intro L
  refine ⟨{1}, ?_, NK.singleton_powerDifferenceFree 2 1, ?_⟩
  · intro a ha
    have h : a = 1 := Finset.mem_singleton.mp ha
    subst a
    simp only [Finset.mem_Icc]
    exact ⟨le_rfl, Nat.one_le_pow L 4 (by decide)⟩
  · simp

-- Exact exponent equality B^alpha = Q is permitted in the arithmetic step.
example (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log 2 N := by
  simpa using NK.rpow_le_mul_pow_log 2 2 N (by decide) hN 1
    (by norm_num) (by norm_num)

-- A false overlarge exponent cannot satisfy the required numerical hypothesis.
example : ¬ ((4 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ)) := by norm_num
