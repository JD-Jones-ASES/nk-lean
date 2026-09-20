import NK.WordGraphCapacity
#print axioms NK.DigraphAlphabet.pullback_moment
#print axioms NK.LexicographicCapacity.capacity_equiv
#print axioms NK.WordGraphCapacity.wordArc_succ
#print axioms NK.WordGraphCapacity.word_capacity
example : NK.LexicographicCapacity.capacity
    (NK.WordGraphCapacity.wordArc (fun _ _ : Fin 0 => False) 0) 1 = 1 := by
  rw [NK.WordGraphCapacity.word_capacity _ 1 (by norm_num)]
  simp
example : NK.LexicographicCapacity.capacity
    (NK.WordGraphCapacity.wordArc (fun _ _ : Fin 0 => False) 3) 1 = 0 := by
  rw [NK.WordGraphCapacity.word_capacity _ 1 (by norm_num),
    NK.LexicographicCapacity.capacity_empty _ 1 (by norm_num)]
  norm_num
example : NK.WordGraphCapacity.wordArc (fun a b : Fin 2 => a = 0 ∧ b = 1) 2 ![0,1] ![1,0] := by
  unfold NK.WordGraphCapacity.wordArc
  decide
example : ¬ NK.WordGraphCapacity.wordArc (fun a b : Fin 2 => a = 0 ∧ b = 1) 2 ![1,0] ![0,1] := by
  unfold NK.WordGraphCapacity.wordArc
  decide
