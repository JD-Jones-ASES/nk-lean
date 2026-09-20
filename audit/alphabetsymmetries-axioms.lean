import NK.AlphabetSymmetries
#print axioms NK.IntervalAlphabet.translate
#print axioms NK.IntervalAlphabet.translate_moment
#print axioms NK.IntervalAlphabet.reflect
#print axioms NK.IntervalAlphabet.reflect_moment
#print axioms NK.IntervalAlphabet.affine
#print axioms NK.IntervalAlphabet.affine_moment
#print axioms NK.AlphabetSymmetries.translate_one_parity
#print axioms NK.AlphabetSymmetries.reflect_parity
#check NK.IntervalAlphabet.mem_translate_support
#check NK.IntervalAlphabet.translate_interval
#check NK.IntervalAlphabet.mem_reflect_support
#check NK.IntervalAlphabet.reflect_interval
-- Empty supports require no positivity hypothesis on their unused modulus.
example : (((NK.IntervalAlphabet.empty 2 0).translate 5).reflect).moment (1/2 : ℝ) = 0 := by simp
-- Translation wraps the top residue and exchanges parity.
example : ((15+1) % 16) % 2 ≠ 15 % 2 :=
  NK.AlphabetSymmetries.translate_one_parity_ne 16 15 (by norm_num)
-- Reflection retains the residue-zero endpoint and odd parity.
example : NK.AlphabetSymmetries.reflectResidue 16 0 = 0 := by norm_num [NK.AlphabetSymmetries.reflectResidue]
example : ((16-3) % 16) % 2 = 3 % 2 :=
  NK.AlphabetSymmetries.reflect_parity 16 3 (by norm_num) (by norm_num)
-- Reversal works for an odd power as well, without assuming antisymmetry.
example : NK.PowerArc 3 16 0 1 := by
  apply NK.AlphabetSymmetries.reflect_arc_reverse 3 16 1 0 (by norm_num) (by norm_num)
  exact ⟨by decide, 1, by decide⟩
