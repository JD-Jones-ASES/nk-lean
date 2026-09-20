import NK.BinarySquares
#print axioms NK.BinarySquares.exists_odd_square_add_three
#print axioms NK.BinarySquares.odd_square_iff_mod_eight
#print axioms NK.BinarySquares.square_four_mul_descent
#check NK.BinarySquares.odd_square_iff_mod_eight
#check NK.BinarySquares.square_four_mul_descent
-- The exponent threshold is essential:5 is a square modulo4 but not1 modulo8.
example : ∃ z : ℕ, (z*z) % 2^2 = 5 % 2^2 := ⟨1, by norm_num⟩
example : (5 : ℕ) % 8 ≠ 1 := by norm_num
-- The odd-unit hypothesis is essential:zero is also a square modulo8.
example : ∃ z : ℕ, (z*z) % 2^3 = 0 % 2^3 := ⟨0, by norm_num⟩
example : (0 : ℕ) % 8 ≠ 1 := by norm_num
-- A nonsquare odd residue is rejected through the public criterion.
example : ¬ ∃ z : ℕ, (z*z) % 2^7 = 3 % 2^7 := by
  intro h
  have hbad := (NK.BinarySquares.odd_square_iff_mod_eight 7 3 (by norm_num) (by norm_num)).mp h
  norm_num at hbad
-- A nonunit square survives the descent, as required by the full relation.
example : ∃ z : ℕ, (z*z) % 4^2 = (4*1) % 4^2 := by
  apply (NK.BinarySquares.square_four_mul_descent 1 1).mpr
  exact ⟨1, by norm_num⟩
