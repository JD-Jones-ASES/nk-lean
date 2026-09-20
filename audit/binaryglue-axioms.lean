import NK.BinaryGlue
#print axioms NK.BinaryGlue.ordered_of_cross_order
#print axioms NK.BinaryGlue.glue
#print axioms NK.BinaryGlue.glue_card
#print axioms NK.BinaryGlue.glue_moment
#check NK.BinaryGlue.glue
#check NK.BinaryGlue.glue_moment
-- Empty children contribute no labelled point, with no nonempty premise.
example {m : ℕ} (A : Fin 4 → NK.IntervalAlphabet 2 (4^m))
    (hEmpty : ∀ r, (A r).support = ∅) : NK.BinaryGlue.support A = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨r, u, hu, _⟩ := (NK.BinaryGlue.mem_support A x).mp hx
  rw [hEmpty r] at hu
  simp at hu
