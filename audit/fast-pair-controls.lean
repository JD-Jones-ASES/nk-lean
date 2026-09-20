import NK.FastPairCertificate

open NK
open NK.PairCertificateTree

example : PowerMaskValid 2 3 2 := by decide +kernel
example : PowerMaskValid 2 5 18 := by decide +kernel
example : PowerMaskValid 2 19 199410 := by decide +kernel
example : PowerMaskValid 2 23 340830 := by decide +kernel
example : PowerMaskValid 2 43 3678700564050 := by decide +kernel
example : ¬ PowerMaskValid 2 3 6 := by decide +kernel
example : ¬ PowerMaskValid 2 43 3678700564051 := by decide +kernel
example : FastPrefixBlocks 3 2 [0, 1] [0, 0] = true := by decide +kernel
example : FastPrefixBlocks 3 2 [0, 0] [0, 1] = false := by decide +kernel
example : FastPrefixBlocks 3 2 [0, 0] [0, 0] = false := by decide +kernel
example : FastPrefixBlocks 3 2 [0] [0, 1] = false := by decide +kernel
example : FastPrefixBlocks 3 2 [0, 1] [0] = false := by decide +kernel
example : FastPrefixBlocks 3 2 [] [1] = false := by decide +kernel
example : FastPrefixBlocks 3 2 [1] [] = false := by decide +kernel
example : CertificatePrefixBlocks 2 3 [0, 1] [0, 0] :=
  fastPrefixBlocks_sound 2 3 2 (by decide) (by decide +kernel) _ _ (by decide +kernel)

private def rowZero : PairCertificateRow := ⟨([0], [0]), 0, 2⟩
private def rowOne : PairCertificateRow := ⟨([1], [1]), 2, 2⟩
private def orderedTree : PairCertificateTree :=
  .branch [] [] 0 (.leaf rowZero) (.leaf rowOne)
example : orderedTree.Valid 3 3 1 10 := by decide +kernel
example : orderedTree.FastGeometryValid 2 3 3 2 2 = true := by decide +kernel
example : orderedTree.GeometryValid 2 3 3 = true :=
  fastGeometryValid_sound 2 3 3 2 2 (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) _ (by decide +kernel)

private def rowOneBad : PairCertificateRow := ⟨([1], [1]), 1, 2⟩
private def overlappingTree : PairCertificateTree :=
  .branch [] [] 0 (.leaf rowZero) (.leaf rowOneBad)
example : overlappingTree.Valid 3 3 1 10 := by decide +kernel
example : overlappingTree.FastGeometryValid 2 3 3 2 2 = false := by decide +kernel

#print axioms NK.fastPrefixBlocks_sound
#print axioms NK.PairCertificateTree.fastQuery_sound
#print axioms NK.PairCertificateTree.fastGeometryValid_sound
