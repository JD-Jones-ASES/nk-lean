import NK.PairCertificateComposition

open NK NK.PairCertificateTree

private def r0 : PairCertificateRow := ⟨([0], [0]), 0, 2⟩
private def r1 : PairCertificateRow := ⟨([1], [1]), 2, 2⟩
private def leftTree : PairCertificateTree := .leaf r0
private def rightTree : PairCertificateTree := .leaf r1
private def tree : PairCertificateTree := .branch [] [] 0 leftTree rightTree
private def treeAlias : PairCertificateTree := tree
private def key (w : RetainedPair) : ℕ := w.1.getD 0 0

example : tree.Valid 3 3 1 10 :=
  valid_of_branch_eq 3 3 1 10 tree [] [] 0 leftTree rightTree rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : tree.Sorted key = true :=
  sorted_of_branch_eq key tree [] [] 0 leftTree rightTree rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem queryAll :
    tree.rows.all (fun s => tree.FastQuery 2 3 3 2 2 s) = true :=
  rows_all_of_branch_eq (fun s => tree.FastQuery 2 3 3 2 2 s)
    tree [] [] 0 leftTree rightTree rfl (by decide +kernel) (by decide +kernel)

example : treeAlias.rows.all (fun s => tree.FastQuery 2 3 3 2 2 s) = true :=
  rows_all_of_eq (fun s => tree.FastQuery 2 3 3 2 2 s) treeAlias tree rfl queryAll

example : tree.FastGeometryValid 2 3 3 2 2 = true :=
  fastGeometry_of_rows_all 2 3 3 2 2 tree queryAll

example : ¬ CertificateWordPrefix [1] leftTree.pPrefix := by decide +kernel
example : ¬ 1 ≤ leftTree.minStart := by decide +kernel
example : ¬ key rightTree.lastWord < key leftTree.firstWord := by decide +kernel
example : tree.rows.all (fun _ => false) = false := by decide +kernel

-- Child-local geometry alone does not certify cross-child arcs.
private def badRight : PairCertificateTree := .leaf ⟨([1], [1]), 1, 2⟩
private def badTree : PairCertificateTree := .branch [] [] 0 leftTree badRight
example : leftTree.FastGeometryValid 2 3 3 2 2 = true := by decide +kernel
example : badRight.FastGeometryValid 2 3 3 2 2 = true := by decide +kernel
example : badTree.Valid 3 3 1 10 := by decide +kernel
example : badTree.FastGeometryValid 2 3 3 2 2 = false := by decide +kernel
example : leftTree.rows.all (fun s => badTree.FastQuery 2 3 3 2 2 s) = false := by decide +kernel

#print axioms NK.PairCertificateTree.valid_of_branch_eq
#print axioms NK.PairCertificateTree.sorted_of_branch_eq
#print axioms NK.PairCertificateTree.rows_all_of_branch_eq
#print axioms NK.PairCertificateTree.rows_all_of_eq
#print axioms NK.PairCertificateTree.fastGeometry_of_rows_all
