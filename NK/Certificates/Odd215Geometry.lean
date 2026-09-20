import NK.Certificates.Odd215Data
import NK.PairCertificateComposition

/-! Literal rows are checked in bounded chunks against the full target tree.
Generic proved assembly combines summaries, uniqueness and every source query. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option Elab.async false
namespace NK.Certificates

theorem odd215_pMask : PowerMaskValid 2 5 18 := by decide +kernel
theorem odd215_qMask : PowerMaskValid 2 43 3678700564050 := by decide +kernel

-- 76 source leaves.
theorem odd215_valid_150 : odd215Tree_150.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_150 : odd215Tree_150.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_150 : odd215Tree_150.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_303 : odd215Tree_303.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_303 : odd215Tree_303.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_303 : odd215Tree_303.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_304 : odd215Tree_304.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_304 [0] [18] 0 odd215Tree_150 odd215Tree_303
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_150 odd215_valid_303

theorem odd215_sorted_304 : odd215Tree_304.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_304 [0] [18] 0 odd215Tree_150 odd215Tree_303
    rfl (by decide +kernel) odd215_sorted_150 odd215_sorted_303

theorem odd215_queries_304 : odd215Tree_304.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_304 [0] [18] 0 odd215Tree_150 odd215Tree_303
    rfl odd215_queries_150 odd215_queries_303

-- 77 source leaves.
theorem odd215_valid_457 : odd215Tree_457.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_457 : odd215Tree_457.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_457 : odd215Tree_457.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_610 : odd215Tree_610.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_610 : odd215Tree_610.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_610 : odd215Tree_610.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_611 : odd215Tree_611.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_611 [0] [] 0 odd215Tree_457 odd215Tree_610
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_457 odd215_valid_610

theorem odd215_sorted_611 : odd215Tree_611.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_611 [0] [] 0 odd215Tree_457 odd215Tree_610
    rfl (by decide +kernel) odd215_sorted_457 odd215_sorted_610

theorem odd215_queries_611 : odd215Tree_611.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_611 [0] [] 0 odd215Tree_457 odd215Tree_610
    rfl odd215_queries_457 odd215_queries_610

-- 307 source leaves.
theorem odd215_valid_612 : odd215Tree_612.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_612 [0] [] 0 odd215Tree_304 odd215Tree_611
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_304 odd215_valid_611

theorem odd215_sorted_612 : odd215Tree_612.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_612 [0] [] 0 odd215Tree_304 odd215Tree_611
    rfl (by decide +kernel) odd215_sorted_304 odd215_sorted_611

theorem odd215_queries_612 : odd215Tree_612.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_612 [0] [] 0 odd215Tree_304 odd215Tree_611
    rfl odd215_queries_304 odd215_queries_611

-- 76 source leaves.
theorem odd215_valid_763 : odd215Tree_763.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_763 : odd215Tree_763.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_763 : odd215Tree_763.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_916 : odd215Tree_916.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_916 : odd215Tree_916.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_916 : odd215Tree_916.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_917 : odd215Tree_917.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_917 [0] [22] 36679784267953 odd215Tree_763 odd215Tree_916
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_763 odd215_valid_916

theorem odd215_sorted_917 : odd215Tree_917.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_917 [0] [22] 36679784267953 odd215Tree_763 odd215Tree_916
    rfl (by decide +kernel) odd215_sorted_763 odd215_sorted_916

theorem odd215_queries_917 : odd215Tree_917.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_917 [0] [22] 36679784267953 odd215Tree_763 odd215Tree_916
    rfl odd215_queries_763 odd215_queries_916

-- 77 source leaves.
theorem odd215_valid_1070 : odd215Tree_1070.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1070 : odd215Tree_1070.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1070 : odd215Tree_1070.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_1223 : odd215Tree_1223.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1223 : odd215Tree_1223.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1223 : odd215Tree_1223.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_1224 : odd215Tree_1224.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1224 [0] [] 23638175824515 odd215Tree_1070 odd215Tree_1223
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1070 odd215_valid_1223

theorem odd215_sorted_1224 : odd215Tree_1224.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1224 [0] [] 23638175824515 odd215Tree_1070 odd215Tree_1223
    rfl (by decide +kernel) odd215_sorted_1070 odd215_sorted_1223

theorem odd215_queries_1224 : odd215Tree_1224.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1224 [0] [] 23638175824515 odd215Tree_1070 odd215Tree_1223
    rfl odd215_queries_1070 odd215_queries_1223

-- 307 source leaves.
theorem odd215_valid_1225 : odd215Tree_1225.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1225 [0] [] 23638175824515 odd215Tree_917 odd215Tree_1224
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_917 odd215_valid_1224

theorem odd215_sorted_1225 : odd215Tree_1225.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1225 [0] [] 23638175824515 odd215Tree_917 odd215Tree_1224
    rfl (by decide +kernel) odd215_sorted_917 odd215_sorted_1224

theorem odd215_queries_1225 : odd215Tree_1225.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1225 [0] [] 23638175824515 odd215Tree_917 odd215Tree_1224
    rfl odd215_queries_917 odd215_queries_1224

-- 614 source leaves.
theorem odd215_valid_1226 : odd215Tree_1226.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1226 [0] [] 0 odd215Tree_612 odd215Tree_1225
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_612 odd215_valid_1225

theorem odd215_sorted_1226 : odd215Tree_1226.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1226 [0] [] 0 odd215Tree_612 odd215Tree_1225
    rfl (by decide +kernel) odd215_sorted_612 odd215_sorted_1225

theorem odd215_queries_1226 : odd215Tree_1226.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1226 [0] [] 0 odd215Tree_612 odd215Tree_1225
    rfl odd215_queries_612 odd215_queries_1225

-- 76 source leaves.
theorem odd215_valid_1377 : odd215Tree_1377.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1377 : odd215Tree_1377.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1377 : odd215Tree_1377.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_1530 : odd215Tree_1530.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1530 : odd215Tree_1530.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1530 : odd215Tree_1530.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_1531 : odd215Tree_1531.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1531 [0] [24] 25034832022912 odd215Tree_1377 odd215Tree_1530
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1377 odd215_valid_1530

theorem odd215_sorted_1531 : odd215Tree_1531.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1531 [0] [24] 25034832022912 odd215Tree_1377 odd215Tree_1530
    rfl (by decide +kernel) odd215_sorted_1377 odd215_sorted_1530

theorem odd215_queries_1531 : odd215Tree_1531.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1531 [0] [24] 25034832022912 odd215Tree_1377 odd215Tree_1530
    rfl odd215_queries_1377 odd215_queries_1530

-- 77 source leaves.
theorem odd215_valid_1684 : odd215Tree_1684.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1684 : odd215Tree_1684.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1684 : odd215Tree_1684.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_1837 : odd215Tree_1837.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1837 : odd215Tree_1837.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1837 : odd215Tree_1837.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_1838 : odd215Tree_1838.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1838 [0] [] 23638175824515 odd215Tree_1684 odd215Tree_1837
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1684 odd215_valid_1837

theorem odd215_sorted_1838 : odd215Tree_1838.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1838 [0] [] 23638175824515 odd215Tree_1684 odd215Tree_1837
    rfl (by decide +kernel) odd215_sorted_1684 odd215_sorted_1837

theorem odd215_queries_1838 : odd215Tree_1838.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1838 [0] [] 23638175824515 odd215Tree_1684 odd215Tree_1837
    rfl odd215_queries_1684 odd215_queries_1837

-- 307 source leaves.
theorem odd215_valid_1839 : odd215Tree_1839.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_1839 [0] [] 23638175824515 odd215Tree_1531 odd215Tree_1838
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1531 odd215_valid_1838

theorem odd215_sorted_1839 : odd215Tree_1839.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_1839 [0] [] 23638175824515 odd215Tree_1531 odd215Tree_1838
    rfl (by decide +kernel) odd215_sorted_1531 odd215_sorted_1838

theorem odd215_queries_1839 : odd215Tree_1839.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_1839 [0] [] 23638175824515 odd215Tree_1531 odd215Tree_1838
    rfl odd215_queries_1531 odd215_queries_1838

-- 76 source leaves.
theorem odd215_valid_1990 : odd215Tree_1990.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_1990 : odd215Tree_1990.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_1990 : odd215Tree_1990.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_2143 : odd215Tree_2143.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2143 : odd215Tree_2143.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2143 : odd215Tree_2143.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_2144 : odd215Tree_2144.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2144 [0] [33] 70468811254205 odd215Tree_1990 odd215Tree_2143
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1990 odd215_valid_2143

theorem odd215_sorted_2144 : odd215Tree_2144.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2144 [0] [33] 70468811254205 odd215Tree_1990 odd215Tree_2143
    rfl (by decide +kernel) odd215_sorted_1990 odd215_sorted_2143

theorem odd215_queries_2144 : odd215Tree_2144.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2144 [0] [33] 70468811254205 odd215Tree_1990 odd215Tree_2143
    rfl odd215_queries_1990 odd215_queries_2143

-- 77 source leaves.
theorem odd215_valid_2297 : odd215Tree_2297.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2297 : odd215Tree_2297.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2297 : odd215Tree_2297.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_2450 : odd215Tree_2450.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2450 : odd215Tree_2450.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2450 : odd215Tree_2450.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_2451 : odd215Tree_2451.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2451 [] [] 47275661158239 odd215Tree_2297 odd215Tree_2450
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2297 odd215_valid_2450

theorem odd215_sorted_2451 : odd215Tree_2451.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2451 [] [] 47275661158239 odd215Tree_2297 odd215Tree_2450
    rfl (by decide +kernel) odd215_sorted_2297 odd215_sorted_2450

theorem odd215_queries_2451 : odd215Tree_2451.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2451 [] [] 47275661158239 odd215Tree_2297 odd215Tree_2450
    rfl odd215_queries_2297 odd215_queries_2450

-- 307 source leaves.
theorem odd215_valid_2452 : odd215Tree_2452.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2452 [] [] 47275661158239 odd215Tree_2144 odd215Tree_2451
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2144 odd215_valid_2451

theorem odd215_sorted_2452 : odd215Tree_2452.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2452 [] [] 47275661158239 odd215Tree_2144 odd215Tree_2451
    rfl (by decide +kernel) odd215_sorted_2144 odd215_sorted_2451

theorem odd215_queries_2452 : odd215Tree_2452.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2452 [] [] 47275661158239 odd215Tree_2144 odd215Tree_2451
    rfl odd215_queries_2144 odd215_queries_2451

-- 614 source leaves.
theorem odd215_valid_2453 : odd215Tree_2453.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2453 [] [] 23638175824515 odd215Tree_1839 odd215Tree_2452
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1839 odd215_valid_2452

theorem odd215_sorted_2453 : odd215Tree_2453.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2453 [] [] 23638175824515 odd215Tree_1839 odd215Tree_2452
    rfl (by decide +kernel) odd215_sorted_1839 odd215_sorted_2452

theorem odd215_queries_2453 : odd215Tree_2453.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2453 [] [] 23638175824515 odd215Tree_1839 odd215Tree_2452
    rfl odd215_queries_1839 odd215_queries_2452

-- 1228 source leaves.
theorem odd215_valid_2454 : odd215Tree_2454.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2454 [] [] 0 odd215Tree_1226 odd215Tree_2453
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_1226 odd215_valid_2453

theorem odd215_sorted_2454 : odd215Tree_2454.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2454 [] [] 0 odd215Tree_1226 odd215Tree_2453
    rfl (by decide +kernel) odd215_sorted_1226 odd215_sorted_2453

theorem odd215_queries_2454 : odd215Tree_2454.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2454 [] [] 0 odd215Tree_1226 odd215Tree_2453
    rfl odd215_queries_1226 odd215_queries_2453

-- 76 source leaves.
theorem odd215_valid_2605 : odd215Tree_2605.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2605 : odd215Tree_2605.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2605 : odd215Tree_2605.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_2758 : odd215Tree_2758.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2758 : odd215Tree_2758.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2758 : odd215Tree_2758.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_2759 : odd215Tree_2759.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_2759 [1] [19] 47275661158239 odd215Tree_2605 odd215Tree_2758
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2605 odd215_valid_2758

theorem odd215_sorted_2759 : odd215Tree_2759.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_2759 [1] [19] 47275661158239 odd215Tree_2605 odd215Tree_2758
    rfl (by decide +kernel) odd215_sorted_2605 odd215_sorted_2758

theorem odd215_queries_2759 : odd215Tree_2759.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_2759 [1] [19] 47275661158239 odd215Tree_2605 odd215Tree_2758
    rfl odd215_queries_2605 odd215_queries_2758

-- 77 source leaves.
theorem odd215_valid_2912 : odd215Tree_2912.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_2912 : odd215Tree_2912.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_2912 : odd215Tree_2912.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_3065 : odd215Tree_3065.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3065 : odd215Tree_3065.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3065 : odd215Tree_3065.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_3066 : odd215Tree_3066.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3066 [1] [] 11818272812744 odd215Tree_2912 odd215Tree_3065
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2912 odd215_valid_3065

theorem odd215_sorted_3066 : odd215Tree_3066.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3066 [1] [] 11818272812744 odd215Tree_2912 odd215Tree_3065
    rfl (by decide +kernel) odd215_sorted_2912 odd215_sorted_3065

theorem odd215_queries_3066 : odd215Tree_3066.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3066 [1] [] 11818272812744 odd215Tree_2912 odd215Tree_3065
    rfl odd215_queries_2912 odd215_queries_3065

-- 307 source leaves.
theorem odd215_valid_3067 : odd215Tree_3067.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3067 [1] [] 11818272812744 odd215Tree_2759 odd215Tree_3066
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2759 odd215_valid_3066

theorem odd215_sorted_3067 : odd215Tree_3067.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3067 [1] [] 11818272812744 odd215Tree_2759 odd215Tree_3066
    rfl (by decide +kernel) odd215_sorted_2759 odd215_sorted_3066

theorem odd215_queries_3067 : odd215Tree_3067.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3067 [1] [] 11818272812744 odd215Tree_2759 odd215Tree_3066
    rfl odd215_queries_2759 odd215_queries_3066

-- 76 source leaves.
theorem odd215_valid_3218 : odd215Tree_3218.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3218 : odd215Tree_3218.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3218 : odd215Tree_3218.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_3371 : odd215Tree_3371.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3371 : odd215Tree_3371.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3371 : odd215Tree_3371.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_3372 : odd215Tree_3372.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3372 [1] [27] 11818272812744 odd215Tree_3218 odd215Tree_3371
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3218 odd215_valid_3371

theorem odd215_sorted_3372 : odd215Tree_3372.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3372 [1] [27] 11818272812744 odd215Tree_3218 odd215Tree_3371
    rfl (by decide +kernel) odd215_sorted_3218 odd215_sorted_3371

theorem odd215_queries_3372 : odd215Tree_3372.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3372 [1] [27] 11818272812744 odd215Tree_3218 odd215Tree_3371
    rfl odd215_queries_3218 odd215_queries_3371

-- 77 source leaves.
theorem odd215_valid_3525 : odd215Tree_3525.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3525 : odd215Tree_3525.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3525 : odd215Tree_3525.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_3678 : odd215Tree_3678.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3678 : odd215Tree_3678.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3678 : odd215Tree_3678.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_3679 : odd215Tree_3679.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3679 [1] [] 13215374502222 odd215Tree_3525 odd215Tree_3678
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3525 odd215_valid_3678

theorem odd215_sorted_3679 : odd215Tree_3679.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3679 [1] [] 13215374502222 odd215Tree_3525 odd215Tree_3678
    rfl (by decide +kernel) odd215_sorted_3525 odd215_sorted_3678

theorem odd215_queries_3679 : odd215Tree_3679.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3679 [1] [] 13215374502222 odd215Tree_3525 odd215Tree_3678
    rfl odd215_queries_3525 odd215_queries_3678

-- 307 source leaves.
theorem odd215_valid_3680 : odd215Tree_3680.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3680 [1] [] 11818272812744 odd215Tree_3372 odd215Tree_3679
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3372 odd215_valid_3679

theorem odd215_sorted_3680 : odd215Tree_3680.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3680 [1] [] 11818272812744 odd215Tree_3372 odd215Tree_3679
    rfl (by decide +kernel) odd215_sorted_3372 odd215_sorted_3679

theorem odd215_queries_3680 : odd215Tree_3680.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3680 [1] [] 11818272812744 odd215Tree_3372 odd215Tree_3679
    rfl odd215_queries_3372 odd215_queries_3679

-- 614 source leaves.
theorem odd215_valid_3681 : odd215Tree_3681.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3681 [1] [] 11818272812744 odd215Tree_3067 odd215Tree_3680
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3067 odd215_valid_3680

theorem odd215_sorted_3681 : odd215Tree_3681.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3681 [1] [] 11818272812744 odd215Tree_3067 odd215Tree_3680
    rfl (by decide +kernel) odd215_sorted_3067 odd215_sorted_3680

theorem odd215_queries_3681 : odd215Tree_3681.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3681 [1] [] 11818272812744 odd215Tree_3067 odd215Tree_3680
    rfl odd215_queries_3067 odd215_queries_3680

-- 76 source leaves.
theorem odd215_valid_3832 : odd215Tree_3832.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3832 : odd215Tree_3832.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3832 : odd215Tree_3832.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_3985 : odd215Tree_3985.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_3985 : odd215Tree_3985.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_3985 : odd215Tree_3985.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_3986 : odd215Tree_3986.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_3986 [1] [28] 80312532205215 odd215Tree_3832 odd215Tree_3985
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3832 odd215_valid_3985

theorem odd215_sorted_3986 : odd215Tree_3986.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_3986 [1] [28] 80312532205215 odd215Tree_3832 odd215Tree_3985
    rfl (by decide +kernel) odd215_sorted_3832 odd215_sorted_3985

theorem odd215_queries_3986 : odd215Tree_3986.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_3986 [1] [28] 80312532205215 odd215Tree_3832 odd215Tree_3985
    rfl odd215_queries_3832 odd215_queries_3985

-- 77 source leaves.
theorem odd215_valid_4139 : odd215Tree_4139.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4139 : odd215Tree_4139.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4139 : odd215Tree_4139.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_4292 : odd215Tree_4292.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4292 : odd215Tree_4292.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4292 : odd215Tree_4292.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_4293 : odd215Tree_4293.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4293 [] [] 35456363703941 odd215Tree_4139 odd215Tree_4292
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4139 odd215_valid_4292

theorem odd215_sorted_4293 : odd215Tree_4293.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4293 [] [] 35456363703941 odd215Tree_4139 odd215Tree_4292
    rfl (by decide +kernel) odd215_sorted_4139 odd215_sorted_4292

theorem odd215_queries_4293 : odd215Tree_4293.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4293 [] [] 35456363703941 odd215Tree_4139 odd215Tree_4292
    rfl odd215_queries_4139 odd215_queries_4292

-- 307 source leaves.
theorem odd215_valid_4294 : odd215Tree_4294.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4294 [] [] 35456363703941 odd215Tree_3986 odd215Tree_4293
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3986 odd215_valid_4293

theorem odd215_sorted_4294 : odd215Tree_4294.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4294 [] [] 35456363703941 odd215Tree_3986 odd215Tree_4293
    rfl (by decide +kernel) odd215_sorted_3986 odd215_sorted_4293

theorem odd215_queries_4294 : odd215Tree_4294.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4294 [] [] 35456363703941 odd215Tree_3986 odd215Tree_4293
    rfl odd215_queries_3986 odd215_queries_4293

-- 76 source leaves.
theorem odd215_valid_4445 : odd215Tree_4445.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4445 : odd215Tree_4445.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4445 : odd215Tree_4445.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_4598 : odd215Tree_4598.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4598 : odd215Tree_4598.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4598 : odd215Tree_4598.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_4599 : odd215Tree_4599.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4599 [2] [5] 35456363703941 odd215Tree_4445 odd215Tree_4598
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4445 odd215_valid_4598

theorem odd215_sorted_4599 : odd215Tree_4599.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4599 [2] [5] 35456363703941 odd215Tree_4445 odd215Tree_4598
    rfl (by decide +kernel) odd215_sorted_4445 odd215_sorted_4598

theorem odd215_queries_4599 : odd215Tree_4599.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4599 [2] [5] 35456363703941 odd215Tree_4445 odd215Tree_4598
    rfl odd215_queries_4445 odd215_queries_4598

-- 77 source leaves.
theorem odd215_valid_4752 : odd215Tree_4752.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4752 : odd215Tree_4752.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4752 : odd215Tree_4752.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_4905 : odd215Tree_4905.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_4905 : odd215Tree_4905.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_4905 : odd215Tree_4905.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_4906 : odd215Tree_4906.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4906 [2] [] 45530472628465 odd215Tree_4752 odd215Tree_4905
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4752 odd215_valid_4905

theorem odd215_sorted_4906 : odd215Tree_4906.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4906 [2] [] 45530472628465 odd215Tree_4752 odd215Tree_4905
    rfl (by decide +kernel) odd215_sorted_4752 odd215_sorted_4905

theorem odd215_queries_4906 : odd215Tree_4906.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4906 [2] [] 45530472628465 odd215Tree_4752 odd215Tree_4905
    rfl odd215_queries_4752 odd215_queries_4905

-- 307 source leaves.
theorem odd215_valid_4907 : odd215Tree_4907.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4907 [2] [] 35456363703941 odd215Tree_4599 odd215Tree_4906
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4599 odd215_valid_4906

theorem odd215_sorted_4907 : odd215Tree_4907.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4907 [2] [] 35456363703941 odd215Tree_4599 odd215Tree_4906
    rfl (by decide +kernel) odd215_sorted_4599 odd215_sorted_4906

theorem odd215_queries_4907 : odd215Tree_4907.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4907 [2] [] 35456363703941 odd215Tree_4599 odd215Tree_4906
    rfl odd215_queries_4599 odd215_queries_4906

-- 614 source leaves.
theorem odd215_valid_4908 : odd215Tree_4908.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4908 [] [] 35456363703941 odd215Tree_4294 odd215Tree_4907
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4294 odd215_valid_4907

theorem odd215_sorted_4908 : odd215Tree_4908.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4908 [] [] 35456363703941 odd215Tree_4294 odd215Tree_4907
    rfl (by decide +kernel) odd215_sorted_4294 odd215_sorted_4907

theorem odd215_queries_4908 : odd215Tree_4908.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4908 [] [] 35456363703941 odd215Tree_4294 odd215Tree_4907
    rfl odd215_queries_4294 odd215_queries_4907

-- 1228 source leaves.
theorem odd215_valid_4909 : odd215Tree_4909.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4909 [] [] 11818272812744 odd215Tree_3681 odd215Tree_4908
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_3681 odd215_valid_4908

theorem odd215_sorted_4909 : odd215Tree_4909.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4909 [] [] 11818272812744 odd215Tree_3681 odd215Tree_4908
    rfl (by decide +kernel) odd215_sorted_3681 odd215_sorted_4908

theorem odd215_queries_4909 : odd215Tree_4909.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4909 [] [] 11818272812744 odd215Tree_3681 odd215Tree_4908
    rfl odd215_queries_3681 odd215_queries_4908

-- 2456 source leaves.
theorem odd215_valid_4910 : odd215Tree_4910.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_4910 [] [] 0 odd215Tree_2454 odd215Tree_4909
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_2454 odd215_valid_4909

theorem odd215_sorted_4910 : odd215Tree_4910.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_4910 [] [] 0 odd215Tree_2454 odd215Tree_4909
    rfl (by decide +kernel) odd215_sorted_2454 odd215_sorted_4909

theorem odd215_queries_4910 : odd215Tree_4910.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_4910 [] [] 0 odd215Tree_2454 odd215Tree_4909
    rfl odd215_queries_2454 odd215_queries_4909

-- 76 source leaves.
theorem odd215_valid_5061 : odd215Tree_5061.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5061 : odd215Tree_5061.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5061 : odd215Tree_5061.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_5214 : odd215Tree_5214.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5214 : odd215Tree_5214.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5214 : odd215Tree_5214.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_5215 : odd215Tree_5215.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_5215 [2] [] 53073948677237 odd215Tree_5061 odd215Tree_5214
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5061 odd215_valid_5214

theorem odd215_sorted_5215 : odd215Tree_5215.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_5215 [2] [] 53073948677237 odd215Tree_5061 odd215Tree_5214
    rfl (by decide +kernel) odd215_sorted_5061 odd215_sorted_5214

theorem odd215_queries_5215 : odd215Tree_5215.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_5215 [2] [] 53073948677237 odd215Tree_5061 odd215Tree_5214
    rfl odd215_queries_5061 odd215_queries_5214

-- 77 source leaves.
theorem odd215_valid_5368 : odd215Tree_5368.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5368 : odd215Tree_5368.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5368 : odd215Tree_5368.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_5521 : odd215Tree_5521.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5521 : odd215Tree_5521.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5521 : odd215Tree_5521.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_5522 : odd215Tree_5522.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_5522 [2] [40] 53073948677237 odd215Tree_5368 odd215Tree_5521
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5368 odd215_valid_5521

theorem odd215_sorted_5522 : odd215Tree_5522.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_5522 [2] [40] 53073948677237 odd215Tree_5368 odd215Tree_5521
    rfl (by decide +kernel) odd215_sorted_5368 odd215_sorted_5521

theorem odd215_queries_5522 : odd215Tree_5522.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_5522 [2] [40] 53073948677237 odd215Tree_5368 odd215Tree_5521
    rfl odd215_queries_5368 odd215_queries_5521

-- 307 source leaves.
theorem odd215_valid_5523 : odd215Tree_5523.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_5523 [2] [] 53073948677237 odd215Tree_5215 odd215Tree_5522
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5215 odd215_valid_5522

theorem odd215_sorted_5523 : odd215Tree_5523.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_5523 [2] [] 53073948677237 odd215Tree_5215 odd215Tree_5522
    rfl (by decide +kernel) odd215_sorted_5215 odd215_sorted_5522

theorem odd215_queries_5523 : odd215Tree_5523.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_5523 [2] [] 53073948677237 odd215Tree_5215 odd215Tree_5522
    rfl odd215_queries_5215 odd215_queries_5522

-- 76 source leaves.
theorem odd215_valid_5674 : odd215Tree_5674.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5674 : odd215Tree_5674.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5674 : odd215Tree_5674.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_5827 : odd215Tree_5827.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5827 : odd215Tree_5827.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5827 : odd215Tree_5827.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_5828 : odd215Tree_5828.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_5828 [] [] 53073948677237 odd215Tree_5674 odd215Tree_5827
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5674 odd215_valid_5827

theorem odd215_sorted_5828 : odd215Tree_5828.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_5828 [] [] 53073948677237 odd215Tree_5674 odd215Tree_5827
    rfl (by decide +kernel) odd215_sorted_5674 odd215_sorted_5827

theorem odd215_queries_5828 : odd215Tree_5828.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_5828 [] [] 53073948677237 odd215Tree_5674 odd215Tree_5827
    rfl odd215_queries_5674 odd215_queries_5827

-- 77 source leaves.
theorem odd215_valid_5981 : odd215Tree_5981.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_5981 : odd215Tree_5981.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_5981 : odd215Tree_5981.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_6134 : odd215Tree_6134.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6134 : odd215Tree_6134.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6134 : odd215Tree_6134.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_6135 : odd215Tree_6135.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6135 [3] [3] 72213766592360 odd215Tree_5981 odd215Tree_6134
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5981 odd215_valid_6134

theorem odd215_sorted_6135 : odd215Tree_6135.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6135 [3] [3] 72213766592360 odd215Tree_5981 odd215Tree_6134
    rfl (by decide +kernel) odd215_sorted_5981 odd215_sorted_6134

theorem odd215_queries_6135 : odd215Tree_6135.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6135 [3] [3] 72213766592360 odd215Tree_5981 odd215Tree_6134
    rfl odd215_queries_5981 odd215_queries_6134

-- 307 source leaves.
theorem odd215_valid_6136 : odd215Tree_6136.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6136 [] [] 53073948677237 odd215Tree_5828 odd215Tree_6135
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5828 odd215_valid_6135

theorem odd215_sorted_6136 : odd215Tree_6136.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6136 [] [] 53073948677237 odd215Tree_5828 odd215Tree_6135
    rfl (by decide +kernel) odd215_sorted_5828 odd215_sorted_6135

theorem odd215_queries_6136 : odd215Tree_6136.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6136 [] [] 53073948677237 odd215Tree_5828 odd215Tree_6135
    rfl odd215_queries_5828 odd215_queries_6135

-- 614 source leaves.
theorem odd215_valid_6137 : odd215Tree_6137.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6137 [] [] 53073948677237 odd215Tree_5523 odd215Tree_6136
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_5523 odd215_valid_6136

theorem odd215_sorted_6137 : odd215Tree_6137.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6137 [] [] 53073948677237 odd215Tree_5523 odd215Tree_6136
    rfl (by decide +kernel) odd215_sorted_5523 odd215_sorted_6136

theorem odd215_queries_6137 : odd215Tree_6137.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6137 [] [] 53073948677237 odd215Tree_5523 odd215Tree_6136
    rfl odd215_queries_5523 odd215_queries_6136

-- 76 source leaves.
theorem odd215_valid_6288 : odd215Tree_6288.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6288 : odd215Tree_6288.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6288 : odd215Tree_6288.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_6441 : odd215Tree_6441.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6441 : odd215Tree_6441.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6441 : odd215Tree_6441.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_6442 : odd215Tree_6442.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6442 [3] [] 58872236196216 odd215Tree_6288 odd215Tree_6441
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6288 odd215_valid_6441

theorem odd215_sorted_6442 : odd215Tree_6442.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6442 [3] [] 58872236196216 odd215Tree_6288 odd215Tree_6441
    rfl (by decide +kernel) odd215_sorted_6288 odd215_sorted_6441

theorem odd215_queries_6442 : odd215Tree_6442.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6442 [3] [] 58872236196216 odd215Tree_6288 odd215Tree_6441
    rfl odd215_queries_6288 odd215_queries_6441

-- 77 source leaves.
theorem odd215_valid_6595 : odd215Tree_6595.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6595 : odd215Tree_6595.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6595 : odd215Tree_6595.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_6748 : odd215Tree_6748.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6748 : odd215Tree_6748.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6748 : odd215Tree_6748.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_6749 : odd215Tree_6749.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6749 [3] [22] 59557460892181 odd215Tree_6595 odd215Tree_6748
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6595 odd215_valid_6748

theorem odd215_sorted_6749 : odd215Tree_6749.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6749 [3] [22] 59557460892181 odd215Tree_6595 odd215Tree_6748
    rfl (by decide +kernel) odd215_sorted_6595 odd215_sorted_6748

theorem odd215_queries_6749 : odd215Tree_6749.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6749 [3] [22] 59557460892181 odd215Tree_6595 odd215Tree_6748
    rfl odd215_queries_6595 odd215_queries_6748

-- 307 source leaves.
theorem odd215_valid_6750 : odd215Tree_6750.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_6750 [3] [] 58872236196216 odd215Tree_6442 odd215Tree_6749
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6442 odd215_valid_6749

theorem odd215_sorted_6750 : odd215Tree_6750.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_6750 [3] [] 58872236196216 odd215Tree_6442 odd215Tree_6749
    rfl (by decide +kernel) odd215_sorted_6442 odd215_sorted_6749

theorem odd215_queries_6750 : odd215Tree_6750.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_6750 [3] [] 58872236196216 odd215Tree_6442 odd215Tree_6749
    rfl odd215_queries_6442 odd215_queries_6749

-- 76 source leaves.
theorem odd215_valid_6901 : odd215Tree_6901.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_6901 : odd215Tree_6901.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_6901 : odd215Tree_6901.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_7054 : odd215Tree_7054.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7054 : odd215Tree_7054.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7054 : odd215Tree_7054.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_7055 : odd215Tree_7055.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7055 [3] [] 0 odd215Tree_6901 odd215Tree_7054
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6901 odd215_valid_7054

theorem odd215_sorted_7055 : odd215Tree_7055.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7055 [3] [] 0 odd215Tree_6901 odd215Tree_7054
    rfl (by decide +kernel) odd215_sorted_6901 odd215_sorted_7054

theorem odd215_queries_7055 : odd215Tree_7055.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7055 [3] [] 0 odd215Tree_6901 odd215Tree_7054
    rfl odd215_queries_6901 odd215_queries_7054

-- 77 source leaves.
theorem odd215_valid_7208 : odd215Tree_7208.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7208 : odd215Tree_7208.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7208 : odd215Tree_7208.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_7361 : odd215Tree_7361.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7361 : odd215Tree_7361.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7361 : odd215Tree_7361.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_7362 : odd215Tree_7362.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7362 [3] [25] 0 odd215Tree_7208 odd215Tree_7361
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7208 odd215_valid_7361

theorem odd215_sorted_7362 : odd215Tree_7362.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7362 [3] [25] 0 odd215Tree_7208 odd215Tree_7361
    rfl (by decide +kernel) odd215_sorted_7208 odd215_sorted_7361

theorem odd215_queries_7362 : odd215Tree_7362.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7362 [3] [25] 0 odd215Tree_7208 odd215Tree_7361
    rfl odd215_queries_7208 odd215_queries_7361

-- 307 source leaves.
theorem odd215_valid_7363 : odd215Tree_7363.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7363 [3] [] 0 odd215Tree_7055 odd215Tree_7362
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7055 odd215_valid_7362

theorem odd215_sorted_7363 : odd215Tree_7363.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7363 [3] [] 0 odd215Tree_7055 odd215Tree_7362
    rfl (by decide +kernel) odd215_sorted_7055 odd215_sorted_7362

theorem odd215_queries_7363 : odd215Tree_7363.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7363 [3] [] 0 odd215Tree_7055 odd215Tree_7362
    rfl odd215_queries_7055 odd215_queries_7362

-- 614 source leaves.
theorem odd215_valid_7364 : odd215Tree_7364.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7364 [3] [] 0 odd215Tree_6750 odd215Tree_7363
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6750 odd215_valid_7363

theorem odd215_sorted_7364 : odd215Tree_7364.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7364 [3] [] 0 odd215Tree_6750 odd215Tree_7363
    rfl (by decide +kernel) odd215_sorted_6750 odd215_sorted_7363

theorem odd215_queries_7364 : odd215Tree_7364.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7364 [3] [] 0 odd215Tree_6750 odd215Tree_7363
    rfl odd215_queries_6750 odd215_queries_7363

-- 1228 source leaves.
theorem odd215_valid_7365 : odd215Tree_7365.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7365 [] [] 0 odd215Tree_6137 odd215Tree_7364
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_6137 odd215_valid_7364

theorem odd215_sorted_7365 : odd215Tree_7365.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7365 [] [] 0 odd215Tree_6137 odd215Tree_7364
    rfl (by decide +kernel) odd215_sorted_6137 odd215_sorted_7364

theorem odd215_queries_7365 : odd215Tree_7365.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7365 [] [] 0 odd215Tree_6137 odd215Tree_7364
    rfl odd215_queries_6137 odd215_queries_7364

-- 76 source leaves.
theorem odd215_valid_7516 : odd215Tree_7516.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7516 : odd215Tree_7516.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7516 : odd215Tree_7516.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_7669 : odd215Tree_7669.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7669 : odd215Tree_7669.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7669 : odd215Tree_7669.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_7670 : odd215Tree_7670.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7670 [3] [] 330191617670 odd215Tree_7516 odd215Tree_7669
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7516 odd215_valid_7669

theorem odd215_sorted_7670 : odd215Tree_7670.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7670 [3] [] 330191617670 odd215Tree_7516 odd215Tree_7669
    rfl (by decide +kernel) odd215_sorted_7516 odd215_sorted_7669

theorem odd215_queries_7670 : odd215Tree_7670.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7670 [3] [] 330191617670 odd215Tree_7516 odd215Tree_7669
    rfl odd215_queries_7516 odd215_queries_7669

-- 77 source leaves.
theorem odd215_valid_7823 : odd215Tree_7823.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7823 : odd215Tree_7823.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7823 : odd215Tree_7823.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_7976 : odd215Tree_7976.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_7976 : odd215Tree_7976.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_7976 : odd215Tree_7976.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_7977 : odd215Tree_7977.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7977 [3] [42] 23637066141511 odd215Tree_7823 odd215Tree_7976
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7823 odd215_valid_7976

theorem odd215_sorted_7977 : odd215Tree_7977.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7977 [3] [42] 23637066141511 odd215Tree_7823 odd215Tree_7976
    rfl (by decide +kernel) odd215_sorted_7823 odd215_sorted_7976

theorem odd215_queries_7977 : odd215Tree_7977.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7977 [3] [42] 23637066141511 odd215Tree_7823 odd215Tree_7976
    rfl odd215_queries_7823 odd215_queries_7976

-- 307 source leaves.
theorem odd215_valid_7978 : odd215Tree_7978.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_7978 [3] [] 330191617670 odd215Tree_7670 odd215Tree_7977
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7670 odd215_valid_7977

theorem odd215_sorted_7978 : odd215Tree_7978.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_7978 [3] [] 330191617670 odd215Tree_7670 odd215Tree_7977
    rfl (by decide +kernel) odd215_sorted_7670 odd215_sorted_7977

theorem odd215_queries_7978 : odd215Tree_7978.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_7978 [3] [] 330191617670 odd215Tree_7670 odd215Tree_7977
    rfl odd215_queries_7670 odd215_queries_7977

-- 76 source leaves.
theorem odd215_valid_8129 : odd215Tree_8129.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8129 : odd215Tree_8129.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8129 : odd215Tree_8129.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_8282 : odd215Tree_8282.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8282 : odd215Tree_8282.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8282 : odd215Tree_8282.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_8283 : odd215Tree_8283.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_8283 [] [] 11819348094729 odd215Tree_8129 odd215Tree_8282
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8129 odd215_valid_8282

theorem odd215_sorted_8283 : odd215Tree_8283.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_8283 [] [] 11819348094729 odd215Tree_8129 odd215Tree_8282
    rfl (by decide +kernel) odd215_sorted_8129 odd215_sorted_8282

theorem odd215_queries_8283 : odd215Tree_8283.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_8283 [] [] 11819348094729 odd215Tree_8129 odd215Tree_8282
    rfl odd215_queries_8129 odd215_queries_8282

-- 77 source leaves.
theorem odd215_valid_8436 : odd215Tree_8436.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8436 : odd215Tree_8436.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8436 : odd215Tree_8436.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_8589 : odd215Tree_8589.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8589 : odd215Tree_8589.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8589 : odd215Tree_8589.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_8590 : odd215Tree_8590.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_8590 [4] [29] 11819348094729 odd215Tree_8436 odd215Tree_8589
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8436 odd215_valid_8589

theorem odd215_sorted_8590 : odd215Tree_8590.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_8590 [4] [29] 11819348094729 odd215Tree_8436 odd215Tree_8589
    rfl (by decide +kernel) odd215_sorted_8436 odd215_sorted_8589

theorem odd215_queries_8590 : odd215Tree_8590.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_8590 [4] [29] 11819348094729 odd215Tree_8436 odd215Tree_8589
    rfl odd215_queries_8436 odd215_queries_8589

-- 307 source leaves.
theorem odd215_valid_8591 : odd215Tree_8591.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_8591 [] [] 11819348094729 odd215Tree_8283 odd215Tree_8590
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8283 odd215_valid_8590

theorem odd215_sorted_8591 : odd215Tree_8591.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_8591 [] [] 11819348094729 odd215Tree_8283 odd215Tree_8590
    rfl (by decide +kernel) odd215_sorted_8283 odd215_sorted_8590

theorem odd215_queries_8591 : odd215Tree_8591.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_8591 [] [] 11819348094729 odd215Tree_8283 odd215Tree_8590
    rfl odd215_queries_8283 odd215_queries_8590

-- 614 source leaves.
theorem odd215_valid_8592 : odd215Tree_8592.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_8592 [] [] 330191617670 odd215Tree_7978 odd215Tree_8591
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7978 odd215_valid_8591

theorem odd215_sorted_8592 : odd215Tree_8592.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_8592 [] [] 330191617670 odd215Tree_7978 odd215Tree_8591
    rfl (by decide +kernel) odd215_sorted_7978 odd215_sorted_8591

theorem odd215_queries_8592 : odd215Tree_8592.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_8592 [] [] 330191617670 odd215Tree_7978 odd215Tree_8591
    rfl odd215_queries_7978 odd215_queries_8591

-- 76 source leaves.
theorem odd215_valid_8743 : odd215Tree_8743.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8743 : odd215Tree_8743.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8743 : odd215Tree_8743.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_8896 : odd215Tree_8896.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_8896 : odd215Tree_8896.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_8896 : odd215Tree_8896.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd215_valid_8897 : odd215Tree_8897.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_8897 [4] [] 13546243038460 odd215Tree_8743 odd215Tree_8896
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8743 odd215_valid_8896

theorem odd215_sorted_8897 : odd215Tree_8897.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_8897 [4] [] 13546243038460 odd215Tree_8743 odd215Tree_8896
    rfl (by decide +kernel) odd215_sorted_8743 odd215_sorted_8896

theorem odd215_queries_8897 : odd215Tree_8897.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_8897 [4] [] 13546243038460 odd215Tree_8743 odd215Tree_8896
    rfl odd215_queries_8743 odd215_queries_8896

-- 77 source leaves.
theorem odd215_valid_9050 : odd215Tree_9050.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9050 : odd215Tree_9050.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9050 : odd215Tree_9050.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_9203 : odd215Tree_9203.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9203 : odd215Tree_9203.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9203 : odd215Tree_9203.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_9204 : odd215Tree_9204.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9204 [4] [35] 64670523715196 odd215Tree_9050 odd215Tree_9203
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_9050 odd215_valid_9203

theorem odd215_sorted_9204 : odd215Tree_9204.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9204 [4] [35] 64670523715196 odd215Tree_9050 odd215Tree_9203
    rfl (by decide +kernel) odd215_sorted_9050 odd215_sorted_9203

theorem odd215_queries_9204 : odd215Tree_9204.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9204 [4] [35] 64670523715196 odd215Tree_9050 odd215Tree_9203
    rfl odd215_queries_9050 odd215_queries_9203

-- 307 source leaves.
theorem odd215_valid_9205 : odd215Tree_9205.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9205 [4] [] 13546243038460 odd215Tree_8897 odd215Tree_9204
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8897 odd215_valid_9204

theorem odd215_sorted_9205 : odd215Tree_9205.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9205 [4] [] 13546243038460 odd215Tree_8897 odd215Tree_9204
    rfl (by decide +kernel) odd215_sorted_8897 odd215_sorted_9204

theorem odd215_queries_9205 : odd215Tree_9205.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9205 [4] [] 13546243038460 odd215Tree_8897 odd215Tree_9204
    rfl odd215_queries_8897 odd215_queries_9204

-- 77 source leaves.
theorem odd215_valid_9358 : odd215Tree_9358.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9358 : odd215Tree_9358.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9358 : odd215Tree_9358.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_9511 : odd215Tree_9511.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9511 : odd215Tree_9511.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9511 : odd215Tree_9511.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_9512 : odd215Tree_9512.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9512 [4] [] 68499769135394 odd215Tree_9358 odd215Tree_9511
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_9358 odd215_valid_9511

theorem odd215_sorted_9512 : odd215Tree_9512.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9512 [4] [] 68499769135394 odd215Tree_9358 odd215Tree_9511
    rfl (by decide +kernel) odd215_sorted_9358 odd215_sorted_9511

theorem odd215_queries_9512 : odd215Tree_9512.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9512 [4] [] 68499769135394 odd215Tree_9358 odd215Tree_9511
    rfl odd215_queries_9358 odd215_queries_9511

-- 77 source leaves.
theorem odd215_valid_9665 : odd215Tree_9665.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9665 : odd215Tree_9665.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9665 : odd215Tree_9665.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd215_valid_9818 : odd215Tree_9818.Valid 5 43 3 99999974386028 := by
  decide +kernel

theorem odd215_sorted_9818 : odd215Tree_9818.Sorted odd215Key = true := by
  decide +kernel

theorem odd215_queries_9818 : odd215Tree_9818.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd215_valid_9819 : odd215Tree_9819.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9819 [4] [39] 85234392840257 odd215Tree_9665 odd215Tree_9818
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_9665 odd215_valid_9818

theorem odd215_sorted_9819 : odd215Tree_9819.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9819 [4] [39] 85234392840257 odd215Tree_9665 odd215Tree_9818
    rfl (by decide +kernel) odd215_sorted_9665 odd215_sorted_9818

theorem odd215_queries_9819 : odd215Tree_9819.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9819 [4] [39] 85234392840257 odd215Tree_9665 odd215Tree_9818
    rfl odd215_queries_9665 odd215_queries_9818

-- 308 source leaves.
theorem odd215_valid_9820 : odd215Tree_9820.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9820 [4] [] 68499769135394 odd215Tree_9512 odd215Tree_9819
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_9512 odd215_valid_9819

theorem odd215_sorted_9820 : odd215Tree_9820.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9820 [4] [] 68499769135394 odd215Tree_9512 odd215Tree_9819
    rfl (by decide +kernel) odd215_sorted_9512 odd215_sorted_9819

theorem odd215_queries_9820 : odd215Tree_9820.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9820 [4] [] 68499769135394 odd215Tree_9512 odd215Tree_9819
    rfl odd215_queries_9512 odd215_queries_9819

-- 615 source leaves.
theorem odd215_valid_9821 : odd215Tree_9821.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9821 [4] [] 13546243038460 odd215Tree_9205 odd215Tree_9820
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_9205 odd215_valid_9820

theorem odd215_sorted_9821 : odd215Tree_9821.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9821 [4] [] 13546243038460 odd215Tree_9205 odd215Tree_9820
    rfl (by decide +kernel) odd215_sorted_9205 odd215_sorted_9820

theorem odd215_queries_9821 : odd215Tree_9821.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9821 [4] [] 13546243038460 odd215Tree_9205 odd215Tree_9820
    rfl odd215_queries_9205 odd215_queries_9820

-- 1229 source leaves.
theorem odd215_valid_9822 : odd215Tree_9822.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9822 [] [] 330191617670 odd215Tree_8592 odd215Tree_9821
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_8592 odd215_valid_9821

theorem odd215_sorted_9822 : odd215Tree_9822.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9822 [] [] 330191617670 odd215Tree_8592 odd215Tree_9821
    rfl (by decide +kernel) odd215_sorted_8592 odd215_sorted_9821

theorem odd215_queries_9822 : odd215Tree_9822.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9822 [] [] 330191617670 odd215Tree_8592 odd215Tree_9821
    rfl odd215_queries_8592 odd215_queries_9821

-- 2457 source leaves.
theorem odd215_valid_9823 : odd215Tree_9823.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9823 [] [] 0 odd215Tree_7365 odd215Tree_9822
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_7365 odd215_valid_9822

theorem odd215_sorted_9823 : odd215Tree_9823.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9823 [] [] 0 odd215Tree_7365 odd215Tree_9822
    rfl (by decide +kernel) odd215_sorted_7365 odd215_sorted_9822

theorem odd215_queries_9823 : odd215Tree_9823.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9823 [] [] 0 odd215Tree_7365 odd215Tree_9822
    rfl odd215_queries_7365 odd215_queries_9822

-- 4913 source leaves.
theorem odd215_valid_9824 : odd215Tree_9824.Valid 5 43 3 99999974386028 := by
  exact PairCertificateTree.valid_of_branch_eq 5 43 3 99999974386028 odd215Tree_9824 [] [] 0 odd215Tree_4910 odd215Tree_9823
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd215_valid_4910 odd215_valid_9823

theorem odd215_sorted_9824 : odd215Tree_9824.Sorted odd215Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd215Key odd215Tree_9824 [] [] 0 odd215Tree_4910 odd215Tree_9823
    rfl (by decide +kernel) odd215_sorted_4910 odd215_sorted_9823

theorem odd215_queries_9824 : odd215Tree_9824.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) odd215Tree_9824 [] [] 0 odd215Tree_4910 odd215Tree_9823
    rfl odd215_queries_4910 odd215_queries_9823

theorem odd215_tree_valid : odd215Tree.Valid 5 43 3 99999974386028 :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.Valid 5 43 3 99999974386028) (show odd215Tree = odd215Tree_9824 from rfl)) odd215_valid_9824

theorem odd215_tree_sorted : odd215Tree.Sorted odd215Key = true :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.Sorted odd215Key = true) (show odd215Tree = odd215Tree_9824 from rfl)) odd215_sorted_9824

theorem odd215_tree_queries : odd215Tree.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.rows.all (fun source => odd215Tree.FastQuery 2 5 43 18 3678700564050 source) = true) (show odd215Tree = odd215Tree_9824 from rfl)) odd215_queries_9824

theorem odd215_tree_geometry : odd215Tree.GeometryValid 2 5 43 = true :=
  PairCertificateTree.fastGeometryValid_sound 2 5 43 18 3678700564050 (by decide) (by decide)
    odd215_pMask odd215_qMask odd215Tree
    (PairCertificateTree.fastGeometry_of_rows_all 2 5 43 18 3678700564050 odd215Tree odd215_tree_queries)

end NK.Certificates
