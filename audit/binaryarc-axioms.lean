import NK.BinaryArc
#print axioms NK.BinaryArc.same_branch_iff
#print axioms NK.BinaryArc.cross_branch_iff
#print axioms NK.BinaryArc.powerArc_fourBranch_iff
#check NK.BinaryArc.powerArc_fourBranch_iff
-- The wrap requires opposite tail parity at modulus16.
example : NK.PowerArc 2 16 3 4 := ⟨by decide, 1, by decide⟩
example : NK.PowerArc 2 16 7 0 := ⟨by decide, 3, by decide⟩
example : ¬ NK.PowerArc 2 16 3 0 := by
  intro h
  have h' := (NK.BinaryArc.powerArc_fourBranch_iff 1 3 0 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp h
  norm_num [NK.BinaryArc.fourBranchArc] at h'
-- Nonunit squares remain in the same-label tail graph.
example : NK.PowerArc 2 16 0 4 := ⟨by decide, 2, by decide⟩
-- m≥1 is essential: modulo4 the wrap exists even with equal tail parity.
example : NK.PowerArc 2 (4^(0+1)) (3+4*0) (0+4*0) := ⟨by decide, 1, by decide⟩
example : ¬ NK.BinaryArc.fourBranchArc 0 3 0 0 0 := by
  norm_num [NK.BinaryArc.fourBranchArc]
