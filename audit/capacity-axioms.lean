import NK.BinaryCapacity
#print axioms NK.BlockComposition.square_mul_descent
#print axioms NK.BlockComposition.ordered
#print axioms NK.BlockComposition.nested_card
#print axioms NK.BlockComposition.nested_moment
#print axioms NK.BinaryCapacity.U_zero
#print axioms NK.BinaryCapacity.U_supermultiplicative
#print axioms NK.BinaryCapacity.two_pow_le_U
#print axioms NK.BinaryCapacity.U_le_four_pow
#print axioms NK.BinaryCapacity.exists_growth_limit
#print axioms NK.BinaryCapacity.capacity_bounds
#print axioms NK.BinaryCapacity.tendsto_capacity
example : NK.BinaryCapacity.U 0 0 = 1 := NK.BinaryCapacity.U_zero 0 (by norm_num)
example : 16 ≤ NK.BinaryCapacity.U 3 4 := by
  have h := NK.BinaryCapacity.two_pow_le_U 3 (by norm_num) 4
  norm_num at h ⊢
  exact h
example : NK.BinaryCapacity.U 0 0 * NK.BinaryCapacity.U 0 2 ≤ NK.BinaryCapacity.U 0 2 := by
  simpa only [Nat.zero_add] using NK.BinaryCapacity.U_supermultiplicative 0 (by norm_num) 0 2
example : ∃ w : ℕ, w*w % 4 = 1 := by
  apply (NK.BlockComposition.square_mul_descent 4 4 2 1 (by norm_num) (by norm_num)).mp
  exact ⟨2, by norm_num⟩
