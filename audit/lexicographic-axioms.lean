import NK.LexicographicCapacity
#print axioms NK.DigraphAlphabet.product_moment
#print axioms NK.IntervalHull.hull_contains
#print axioms NK.IntervalHull.right_le_left
#print axioms NK.DigraphAlphabet.normalize_moment
#print axioms NK.LexicographicCapacity.outer
#print axioms NK.LexicographicCapacity.fiber_moment_le
#print axioms NK.LexicographicCapacity.capacity_lex
#print axioms NK.LexicographicCapacity.capacity_empty
#print axioms NK.LexicographicCapacity.capacity_edgeless
example (G : Fin 0 → Fin 0 → Prop) : NK.LexicographicCapacity.capacity G 0 = 0 :=
  NK.LexicographicCapacity.capacity_empty G 0 (by norm_num)
example : NK.LexicographicCapacity.capacity (fun _ _ : Fin 3 => False) 2 = 3 := by
  simpa using NK.LexicographicCapacity.capacity_edgeless (V := Fin 3) 2 (by norm_num)
example (G : Fin 0 → Fin 0 → Prop) (H : Fin 2 → Fin 2 → Prop) :
    NK.LexicographicCapacity.capacity (NK.DigraphAlphabet.lex G H) 0 = 0 := by
  rw [NK.LexicographicCapacity.capacity_lex G H 0 (by norm_num),
    NK.LexicographicCapacity.capacity_empty G 0 (by norm_num), zero_mul]
example (G H : Fin 2 → Fin 2 → Prop) :
    NK.LexicographicCapacity.capacity (NK.DigraphAlphabet.lex G H) 0 =
      NK.LexicographicCapacity.capacity G 0 * NK.LexicographicCapacity.capacity H 0 :=
  NK.LexicographicCapacity.capacity_lex G H 0 (by norm_num)
-- Nonempty vertex type can still have zero capacity: every vertex has a loop.
example : NK.LexicographicCapacity.capacity (fun _ _ : Fin 1 => True) 0 = 0 := by
  apply le_antisymm
  · apply csSup_le (NK.LexicographicCapacity.momentSet_nonempty _ 0)
    rintro z ⟨A,rfl⟩
    have hn : ∀ x, A.interval x = none := by
      intro x
      cases hx : A.interval x with
      | none => rfl
      | some I =>
        have h := A.ordered x x I I hx hx trivial
        have hp := I.width_pos
        linarith
    simp only [NK.DigraphAlphabet.moment, hn, NK.DigraphAlphabet.weight, Finset.sum_const_zero, le_refl]
  · exact NK.LexicographicCapacity.capacity_nonneg _ 0 (by norm_num)
