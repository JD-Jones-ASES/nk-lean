import NK.Certificates.Odd437Data
import NK.PairCertificateComposition

/-! Literal rows are checked in bounded chunks against the full target tree.
Generic proved assembly combines summaries, uniqueness and every source query. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option Elab.async false
namespace NK.Certificates

theorem odd437_pMask : PowerMaskValid 2 19 199410 := by decide +kernel
theorem odd437_qMask : PowerMaskValid 2 23 340830 := by decide +kernel

-- 76 source leaves.
theorem odd437_valid_150 : odd437Tree_150.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_150 : odd437Tree_150.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_150 : odd437Tree_150.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_303 : odd437Tree_303.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_303 : odd437Tree_303.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_303 : odd437Tree_303.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_304 : odd437Tree_304.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_304 [0] [5] 87636488919665 odd437Tree_150 odd437Tree_303
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_150 odd437_valid_303

theorem odd437_sorted_304 : odd437Tree_304.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_304 [0] [5] 87636488919665 odd437Tree_150 odd437Tree_303
    rfl (by decide +kernel) odd437_sorted_150 odd437_sorted_303

theorem odd437_queries_304 : odd437Tree_304.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_304 [0] [5] 87636488919665 odd437Tree_150 odd437Tree_303
    rfl odd437_queries_150 odd437_queries_303

-- 77 source leaves.
theorem odd437_valid_457 : odd437Tree_457.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_457 : odd437Tree_457.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_457 : odd437Tree_457.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_610 : odd437Tree_610.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_610 : odd437Tree_610.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_610 : odd437Tree_610.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_611 : odd437Tree_611.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_611 [0] [5] 87636488919665 odd437Tree_457 odd437Tree_610
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_457 odd437_valid_610

theorem odd437_sorted_611 : odd437Tree_611.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_611 [0] [5] 87636488919665 odd437Tree_457 odd437Tree_610
    rfl (by decide +kernel) odd437_sorted_457 odd437_sorted_610

theorem odd437_queries_611 : odd437Tree_611.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_611 [0] [5] 87636488919665 odd437Tree_457 odd437Tree_610
    rfl odd437_queries_457 odd437_queries_610

-- 307 source leaves.
theorem odd437_valid_612 : odd437Tree_612.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_612 [0] [5] 87636488919665 odd437Tree_304 odd437Tree_611
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_304 odd437_valid_611

theorem odd437_sorted_612 : odd437Tree_612.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_612 [0] [5] 87636488919665 odd437Tree_304 odd437Tree_611
    rfl (by decide +kernel) odd437_sorted_304 odd437_sorted_611

theorem odd437_queries_612 : odd437Tree_612.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_612 [0] [5] 87636488919665 odd437Tree_304 odd437Tree_611
    rfl odd437_queries_304 odd437_queries_611

-- 77 source leaves.
theorem odd437_valid_765 : odd437Tree_765.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_765 : odd437Tree_765.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_765 : odd437Tree_765.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_918 : odd437Tree_918.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_918 : odd437Tree_918.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_918 : odd437Tree_918.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_919 : odd437Tree_919.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_919 [0] [5] 87907570689409 odd437Tree_765 odd437Tree_918
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_765 odd437_valid_918

theorem odd437_sorted_919 : odd437Tree_919.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_919 [0] [5] 87907570689409 odd437Tree_765 odd437Tree_918
    rfl (by decide +kernel) odd437_sorted_765 odd437_sorted_918

theorem odd437_queries_919 : odd437Tree_919.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_919 [0] [5] 87907570689409 odd437Tree_765 odd437Tree_918
    rfl odd437_queries_765 odd437_queries_918

-- 77 source leaves.
theorem odd437_valid_1072 : odd437Tree_1072.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1072 : odd437Tree_1072.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1072 : odd437Tree_1072.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_1225 : odd437Tree_1225.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1225 : odd437Tree_1225.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1225 : odd437Tree_1225.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_1226 : odd437Tree_1226.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1226 [0] [5] 90213398734319 odd437Tree_1072 odd437Tree_1225
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1072 odd437_valid_1225

theorem odd437_sorted_1226 : odd437Tree_1226.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1226 [0] [5] 90213398734319 odd437Tree_1072 odd437Tree_1225
    rfl (by decide +kernel) odd437_sorted_1072 odd437_sorted_1225

theorem odd437_queries_1226 : odd437Tree_1226.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1226 [0] [5] 90213398734319 odd437Tree_1072 odd437Tree_1225
    rfl odd437_queries_1072 odd437_queries_1225

-- 308 source leaves.
theorem odd437_valid_1227 : odd437Tree_1227.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1227 [0] [5] 87907570689409 odd437Tree_919 odd437Tree_1226
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_919 odd437_valid_1226

theorem odd437_sorted_1227 : odd437Tree_1227.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1227 [0] [5] 87907570689409 odd437Tree_919 odd437Tree_1226
    rfl (by decide +kernel) odd437_sorted_919 odd437_sorted_1226

theorem odd437_queries_1227 : odd437Tree_1227.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1227 [0] [5] 87907570689409 odd437Tree_919 odd437Tree_1226
    rfl odd437_queries_919 odd437_queries_1226

-- 615 source leaves.
theorem odd437_valid_1228 : odd437Tree_1228.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1228 [0] [5] 87636488919665 odd437Tree_612 odd437Tree_1227
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_612 odd437_valid_1227

theorem odd437_sorted_1228 : odd437Tree_1228.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1228 [0] [5] 87636488919665 odd437Tree_612 odd437Tree_1227
    rfl (by decide +kernel) odd437_sorted_612 odd437_sorted_1227

theorem odd437_queries_1228 : odd437Tree_1228.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1228 [0] [5] 87636488919665 odd437Tree_612 odd437Tree_1227
    rfl odd437_queries_612 odd437_queries_1227

-- 76 source leaves.
theorem odd437_valid_1379 : odd437Tree_1379.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1379 : odd437Tree_1379.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1379 : odd437Tree_1379.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_1532 : odd437Tree_1532.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1532 : odd437Tree_1532.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1532 : odd437Tree_1532.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_1533 : odd437Tree_1533.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1533 [0] [] 0 odd437Tree_1379 odd437Tree_1532
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1379 odd437_valid_1532

theorem odd437_sorted_1533 : odd437Tree_1533.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1533 [0] [] 0 odd437Tree_1379 odd437Tree_1532
    rfl (by decide +kernel) odd437_sorted_1379 odd437_sorted_1532

theorem odd437_queries_1533 : odd437Tree_1533.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1533 [0] [] 0 odd437Tree_1379 odd437Tree_1532
    rfl odd437_queries_1379 odd437_queries_1532

-- 77 source leaves.
theorem odd437_valid_1686 : odd437Tree_1686.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1686 : odd437Tree_1686.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1686 : odd437Tree_1686.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_1839 : odd437Tree_1839.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1839 : odd437Tree_1839.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1839 : odd437Tree_1839.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_1840 : odd437Tree_1840.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1840 [0] [16] 0 odd437Tree_1686 odd437Tree_1839
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1686 odd437_valid_1839

theorem odd437_sorted_1840 : odd437Tree_1840.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1840 [0] [16] 0 odd437Tree_1686 odd437Tree_1839
    rfl (by decide +kernel) odd437_sorted_1686 odd437_sorted_1839

theorem odd437_queries_1840 : odd437Tree_1840.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1840 [0] [16] 0 odd437Tree_1686 odd437Tree_1839
    rfl odd437_queries_1686 odd437_queries_1839

-- 307 source leaves.
theorem odd437_valid_1841 : odd437Tree_1841.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_1841 [0] [] 0 odd437Tree_1533 odd437Tree_1840
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1533 odd437_valid_1840

theorem odd437_sorted_1841 : odd437Tree_1841.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_1841 [0] [] 0 odd437Tree_1533 odd437Tree_1840
    rfl (by decide +kernel) odd437_sorted_1533 odd437_sorted_1840

theorem odd437_queries_1841 : odd437Tree_1841.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_1841 [0] [] 0 odd437Tree_1533 odd437Tree_1840
    rfl odd437_queries_1533 odd437_queries_1840

-- 77 source leaves.
theorem odd437_valid_1994 : odd437Tree_1994.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_1994 : odd437Tree_1994.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_1994 : odd437Tree_1994.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_2147 : odd437Tree_2147.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2147 : odd437Tree_2147.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2147 : odd437Tree_2147.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_2148 : odd437Tree_2148.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2148 [0] [16] 0 odd437Tree_1994 odd437Tree_2147
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1994 odd437_valid_2147

theorem odd437_sorted_2148 : odd437Tree_2148.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2148 [0] [16] 0 odd437Tree_1994 odd437Tree_2147
    rfl (by decide +kernel) odd437_sorted_1994 odd437_sorted_2147

theorem odd437_queries_2148 : odd437Tree_2148.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2148 [0] [16] 0 odd437Tree_1994 odd437Tree_2147
    rfl odd437_queries_1994 odd437_queries_2147

-- 77 source leaves.
theorem odd437_valid_2301 : odd437Tree_2301.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2301 : odd437Tree_2301.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2301 : odd437Tree_2301.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_2454 : odd437Tree_2454.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2454 : odd437Tree_2454.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2454 : odd437Tree_2454.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_2455 : odd437Tree_2455.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2455 [0] [16] 606091831132 odd437Tree_2301 odd437Tree_2454
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2301 odd437_valid_2454

theorem odd437_sorted_2455 : odd437Tree_2455.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2455 [0] [16] 606091831132 odd437Tree_2301 odd437Tree_2454
    rfl (by decide +kernel) odd437_sorted_2301 odd437_sorted_2454

theorem odd437_queries_2455 : odd437Tree_2455.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2455 [0] [16] 606091831132 odd437Tree_2301 odd437Tree_2454
    rfl odd437_queries_2301 odd437_queries_2454

-- 308 source leaves.
theorem odd437_valid_2456 : odd437Tree_2456.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2456 [0] [16] 0 odd437Tree_2148 odd437Tree_2455
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2148 odd437_valid_2455

theorem odd437_sorted_2456 : odd437Tree_2456.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2456 [0] [16] 0 odd437Tree_2148 odd437Tree_2455
    rfl (by decide +kernel) odd437_sorted_2148 odd437_sorted_2455

theorem odd437_queries_2456 : odd437Tree_2456.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2456 [0] [16] 0 odd437Tree_2148 odd437Tree_2455
    rfl odd437_queries_2148 odd437_queries_2455

-- 615 source leaves.
theorem odd437_valid_2457 : odd437Tree_2457.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2457 [0] [] 0 odd437Tree_1841 odd437Tree_2456
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1841 odd437_valid_2456

theorem odd437_sorted_2457 : odd437Tree_2457.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2457 [0] [] 0 odd437Tree_1841 odd437Tree_2456
    rfl (by decide +kernel) odd437_sorted_1841 odd437_sorted_2456

theorem odd437_queries_2457 : odd437Tree_2457.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2457 [0] [] 0 odd437Tree_1841 odd437Tree_2456
    rfl odd437_queries_1841 odd437_queries_2456

-- 1230 source leaves.
theorem odd437_valid_2458 : odd437Tree_2458.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2458 [0] [] 0 odd437Tree_1228 odd437Tree_2457
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_1228 odd437_valid_2457

theorem odd437_sorted_2458 : odd437Tree_2458.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2458 [0] [] 0 odd437Tree_1228 odd437Tree_2457
    rfl (by decide +kernel) odd437_sorted_1228 odd437_sorted_2457

theorem odd437_queries_2458 : odd437Tree_2458.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2458 [0] [] 0 odd437Tree_1228 odd437Tree_2457
    rfl odd437_queries_1228 odd437_queries_2457

-- 76 source leaves.
theorem odd437_valid_2609 : odd437Tree_2609.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2609 : odd437Tree_2609.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2609 : odd437Tree_2609.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_2762 : odd437Tree_2762.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2762 : odd437Tree_2762.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2762 : odd437Tree_2762.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_2763 : odd437Tree_2763.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_2763 [0] [16] 5761510874748 odd437Tree_2609 odd437Tree_2762
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2609 odd437_valid_2762

theorem odd437_sorted_2763 : odd437Tree_2763.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_2763 [0] [16] 5761510874748 odd437Tree_2609 odd437Tree_2762
    rfl (by decide +kernel) odd437_sorted_2609 odd437_sorted_2762

theorem odd437_queries_2763 : odd437Tree_2763.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_2763 [0] [16] 5761510874748 odd437Tree_2609 odd437Tree_2762
    rfl odd437_queries_2609 odd437_queries_2762

-- 77 source leaves.
theorem odd437_valid_2916 : odd437Tree_2916.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_2916 : odd437Tree_2916.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_2916 : odd437Tree_2916.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_3069 : odd437Tree_3069.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3069 : odd437Tree_3069.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3069 : odd437Tree_3069.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_3070 : odd437Tree_3070.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3070 [0] [] 7397997988688 odd437Tree_2916 odd437Tree_3069
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2916 odd437_valid_3069

theorem odd437_sorted_3070 : odd437Tree_3070.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3070 [0] [] 7397997988688 odd437Tree_2916 odd437Tree_3069
    rfl (by decide +kernel) odd437_sorted_2916 odd437_sorted_3069

theorem odd437_queries_3070 : odd437Tree_3070.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3070 [0] [] 7397997988688 odd437Tree_2916 odd437Tree_3069
    rfl odd437_queries_2916 odd437_queries_3069

-- 307 source leaves.
theorem odd437_valid_3071 : odd437Tree_3071.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3071 [0] [] 5761510874748 odd437Tree_2763 odd437Tree_3070
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2763 odd437_valid_3070

theorem odd437_sorted_3071 : odd437Tree_3071.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3071 [0] [] 5761510874748 odd437Tree_2763 odd437Tree_3070
    rfl (by decide +kernel) odd437_sorted_2763 odd437_sorted_3070

theorem odd437_queries_3071 : odd437Tree_3071.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3071 [0] [] 5761510874748 odd437Tree_2763 odd437Tree_3070
    rfl odd437_queries_2763 odd437_queries_3070

-- 77 source leaves.
theorem odd437_valid_3224 : odd437Tree_3224.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3224 : odd437Tree_3224.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3224 : odd437Tree_3224.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_3377 : odd437Tree_3377.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3377 : odd437Tree_3377.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3377 : odd437Tree_3377.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_3378 : odd437Tree_3378.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3378 [0] [19] 21359226082718 odd437Tree_3224 odd437Tree_3377
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3224 odd437_valid_3377

theorem odd437_sorted_3378 : odd437Tree_3378.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3378 [0] [19] 21359226082718 odd437Tree_3224 odd437Tree_3377
    rfl (by decide +kernel) odd437_sorted_3224 odd437_sorted_3377

theorem odd437_queries_3378 : odd437Tree_3378.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3378 [0] [19] 21359226082718 odd437Tree_3224 odd437Tree_3377
    rfl odd437_queries_3224 odd437_queries_3377

-- 77 source leaves.
theorem odd437_valid_3531 : odd437Tree_3531.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3531 : odd437Tree_3531.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3531 : odd437Tree_3531.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_3684 : odd437Tree_3684.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3684 : odd437Tree_3684.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3684 : odd437Tree_3684.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_3685 : odd437Tree_3685.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3685 [0] [19] 21018810613916 odd437Tree_3531 odd437Tree_3684
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3531 odd437_valid_3684

theorem odd437_sorted_3685 : odd437Tree_3685.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3685 [0] [19] 21018810613916 odd437Tree_3531 odd437Tree_3684
    rfl (by decide +kernel) odd437_sorted_3531 odd437_sorted_3684

theorem odd437_queries_3685 : odd437Tree_3685.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3685 [0] [19] 21018810613916 odd437Tree_3531 odd437Tree_3684
    rfl odd437_queries_3531 odd437_queries_3684

-- 308 source leaves.
theorem odd437_valid_3686 : odd437Tree_3686.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3686 [0] [19] 21018810613916 odd437Tree_3378 odd437Tree_3685
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3378 odd437_valid_3685

theorem odd437_sorted_3686 : odd437Tree_3686.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3686 [0] [19] 21018810613916 odd437Tree_3378 odd437Tree_3685
    rfl (by decide +kernel) odd437_sorted_3378 odd437_sorted_3685

theorem odd437_queries_3686 : odd437Tree_3686.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3686 [0] [19] 21018810613916 odd437Tree_3378 odd437Tree_3685
    rfl odd437_queries_3378 odd437_queries_3685

-- 615 source leaves.
theorem odd437_valid_3687 : odd437Tree_3687.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3687 [0] [] 5761510874748 odd437Tree_3071 odd437Tree_3686
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3071 odd437_valid_3686

theorem odd437_sorted_3687 : odd437Tree_3687.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3687 [0] [] 5761510874748 odd437Tree_3071 odd437Tree_3686
    rfl (by decide +kernel) odd437_sorted_3071 odd437_sorted_3686

theorem odd437_queries_3687 : odd437Tree_3687.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3687 [0] [] 5761510874748 odd437Tree_3071 odd437Tree_3686
    rfl odd437_queries_3071 odd437_queries_3686

-- 76 source leaves.
theorem odd437_valid_3838 : odd437Tree_3838.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3838 : odd437Tree_3838.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3838 : odd437Tree_3838.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_3991 : odd437Tree_3991.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_3991 : odd437Tree_3991.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_3991 : odd437Tree_3991.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_3992 : odd437Tree_3992.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_3992 [0] [19] 21662789591417 odd437Tree_3838 odd437Tree_3991
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3838 odd437_valid_3991

theorem odd437_sorted_3992 : odd437Tree_3992.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_3992 [0] [19] 21662789591417 odd437Tree_3838 odd437Tree_3991
    rfl (by decide +kernel) odd437_sorted_3838 odd437_sorted_3991

theorem odd437_queries_3992 : odd437Tree_3992.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_3992 [0] [19] 21662789591417 odd437Tree_3838 odd437Tree_3991
    rfl odd437_queries_3838 odd437_queries_3991

-- 77 source leaves.
theorem odd437_valid_4145 : odd437Tree_4145.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4145 : odd437Tree_4145.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4145 : odd437Tree_4145.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_4298 : odd437Tree_4298.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4298 : odd437Tree_4298.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4298 : odd437Tree_4298.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_4299 : odd437Tree_4299.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4299 [0] [19] 21326460016761 odd437Tree_4145 odd437Tree_4298
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4145 odd437_valid_4298

theorem odd437_sorted_4299 : odd437Tree_4299.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4299 [0] [19] 21326460016761 odd437Tree_4145 odd437Tree_4298
    rfl (by decide +kernel) odd437_sorted_4145 odd437_sorted_4298

theorem odd437_queries_4299 : odd437Tree_4299.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4299 [0] [19] 21326460016761 odd437Tree_4145 odd437Tree_4298
    rfl odd437_queries_4145 odd437_queries_4298

-- 307 source leaves.
theorem odd437_valid_4300 : odd437Tree_4300.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4300 [0] [19] 21326460016761 odd437Tree_3992 odd437Tree_4299
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3992 odd437_valid_4299

theorem odd437_sorted_4300 : odd437Tree_4300.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4300 [0] [19] 21326460016761 odd437Tree_3992 odd437Tree_4299
    rfl (by decide +kernel) odd437_sorted_3992 odd437_sorted_4299

theorem odd437_queries_4300 : odd437Tree_4300.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4300 [0] [19] 21326460016761 odd437Tree_3992 odd437Tree_4299
    rfl odd437_queries_3992 odd437_queries_4299

-- 77 source leaves.
theorem odd437_valid_4453 : odd437Tree_4453.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4453 : odd437Tree_4453.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4453 : odd437Tree_4453.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_4606 : odd437Tree_4606.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4606 : odd437Tree_4606.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4606 : odd437Tree_4606.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_4607 : odd437Tree_4607.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4607 [0] [] 25447238678662 odd437Tree_4453 odd437Tree_4606
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4453 odd437_valid_4606

theorem odd437_sorted_4607 : odd437Tree_4607.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4607 [0] [] 25447238678662 odd437Tree_4453 odd437Tree_4606
    rfl (by decide +kernel) odd437_sorted_4453 odd437_sorted_4606

theorem odd437_queries_4607 : odd437Tree_4607.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4607 [0] [] 25447238678662 odd437Tree_4453 odd437Tree_4606
    rfl odd437_queries_4453 odd437_queries_4606

-- 77 source leaves.
theorem odd437_valid_4760 : odd437Tree_4760.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4760 : odd437Tree_4760.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4760 : odd437Tree_4760.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_4913 : odd437Tree_4913.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_4913 : odd437Tree_4913.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_4913 : odd437Tree_4913.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_4914 : odd437Tree_4914.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4914 [0] [20] 28847260776858 odd437Tree_4760 odd437Tree_4913
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4760 odd437_valid_4913

theorem odd437_sorted_4914 : odd437Tree_4914.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4914 [0] [20] 28847260776858 odd437Tree_4760 odd437Tree_4913
    rfl (by decide +kernel) odd437_sorted_4760 odd437_sorted_4913

theorem odd437_queries_4914 : odd437Tree_4914.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4914 [0] [20] 28847260776858 odd437Tree_4760 odd437Tree_4913
    rfl odd437_queries_4760 odd437_queries_4913

-- 308 source leaves.
theorem odd437_valid_4915 : odd437Tree_4915.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4915 [0] [] 25447238678662 odd437Tree_4607 odd437Tree_4914
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4607 odd437_valid_4914

theorem odd437_sorted_4915 : odd437Tree_4915.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4915 [0] [] 25447238678662 odd437Tree_4607 odd437Tree_4914
    rfl (by decide +kernel) odd437_sorted_4607 odd437_sorted_4914

theorem odd437_queries_4915 : odd437Tree_4915.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4915 [0] [] 25447238678662 odd437Tree_4607 odd437Tree_4914
    rfl odd437_queries_4607 odd437_queries_4914

-- 615 source leaves.
theorem odd437_valid_4916 : odd437Tree_4916.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4916 [0] [] 21326460016761 odd437Tree_4300 odd437Tree_4915
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4300 odd437_valid_4915

theorem odd437_sorted_4916 : odd437Tree_4916.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4916 [0] [] 21326460016761 odd437Tree_4300 odd437Tree_4915
    rfl (by decide +kernel) odd437_sorted_4300 odd437_sorted_4915

theorem odd437_queries_4916 : odd437Tree_4916.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4916 [0] [] 21326460016761 odd437Tree_4300 odd437Tree_4915
    rfl odd437_queries_4300 odd437_queries_4915

-- 1230 source leaves.
theorem odd437_valid_4917 : odd437Tree_4917.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4917 [0] [] 5761510874748 odd437Tree_3687 odd437Tree_4916
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_3687 odd437_valid_4916

theorem odd437_sorted_4917 : odd437Tree_4917.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4917 [0] [] 5761510874748 odd437Tree_3687 odd437Tree_4916
    rfl (by decide +kernel) odd437_sorted_3687 odd437_sorted_4916

theorem odd437_queries_4917 : odd437Tree_4917.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4917 [0] [] 5761510874748 odd437Tree_3687 odd437Tree_4916
    rfl odd437_queries_3687 odd437_queries_4916

-- 2460 source leaves.
theorem odd437_valid_4918 : odd437Tree_4918.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_4918 [0] [] 0 odd437Tree_2458 odd437Tree_4917
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_2458 odd437_valid_4917

theorem odd437_sorted_4918 : odd437Tree_4918.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_4918 [0] [] 0 odd437Tree_2458 odd437Tree_4917
    rfl (by decide +kernel) odd437_sorted_2458 odd437_sorted_4917

theorem odd437_queries_4918 : odd437Tree_4918.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_4918 [0] [] 0 odd437Tree_2458 odd437Tree_4917
    rfl odd437_queries_2458 odd437_queries_4917

-- 76 source leaves.
theorem odd437_valid_5069 : odd437Tree_5069.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5069 : odd437Tree_5069.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5069 : odd437Tree_5069.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_5222 : odd437Tree_5222.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5222 : odd437Tree_5222.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5222 : odd437Tree_5222.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_5223 : odd437Tree_5223.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_5223 [0] [20] 28107992424177 odd437Tree_5069 odd437Tree_5222
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5069 odd437_valid_5222

theorem odd437_sorted_5223 : odd437Tree_5223.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_5223 [0] [20] 28107992424177 odd437Tree_5069 odd437Tree_5222
    rfl (by decide +kernel) odd437_sorted_5069 odd437_sorted_5222

theorem odd437_queries_5223 : odd437Tree_5223.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_5223 [0] [20] 28107992424177 odd437Tree_5069 odd437Tree_5222
    rfl odd437_queries_5069 odd437_queries_5222

-- 77 source leaves.
theorem odd437_valid_5376 : odd437Tree_5376.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5376 : odd437Tree_5376.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5376 : odd437Tree_5376.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_5529 : odd437Tree_5529.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5529 : odd437Tree_5529.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5529 : odd437Tree_5529.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_5530 : odd437Tree_5530.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_5530 [0] [20] 28031394617898 odd437Tree_5376 odd437Tree_5529
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5376 odd437_valid_5529

theorem odd437_sorted_5530 : odd437Tree_5530.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_5530 [0] [20] 28031394617898 odd437Tree_5376 odd437Tree_5529
    rfl (by decide +kernel) odd437_sorted_5376 odd437_sorted_5529

theorem odd437_queries_5530 : odd437Tree_5530.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_5530 [0] [20] 28031394617898 odd437Tree_5376 odd437Tree_5529
    rfl odd437_queries_5376 odd437_queries_5529

-- 307 source leaves.
theorem odd437_valid_5531 : odd437Tree_5531.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_5531 [0] [20] 28031394617898 odd437Tree_5223 odd437Tree_5530
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5223 odd437_valid_5530

theorem odd437_sorted_5531 : odd437Tree_5531.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_5531 [0] [20] 28031394617898 odd437Tree_5223 odd437Tree_5530
    rfl (by decide +kernel) odd437_sorted_5223 odd437_sorted_5530

theorem odd437_queries_5531 : odd437Tree_5531.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_5531 [0] [20] 28031394617898 odd437Tree_5223 odd437Tree_5530
    rfl odd437_queries_5223 odd437_queries_5530

-- 77 source leaves.
theorem odd437_valid_5684 : odd437Tree_5684.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5684 : odd437Tree_5684.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5684 : odd437Tree_5684.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_5837 : odd437Tree_5837.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5837 : odd437Tree_5837.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5837 : odd437Tree_5837.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_5838 : odd437Tree_5838.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_5838 [] [] 32311676421860 odd437Tree_5684 odd437Tree_5837
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5684 odd437_valid_5837

theorem odd437_sorted_5838 : odd437Tree_5838.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_5838 [] [] 32311676421860 odd437Tree_5684 odd437Tree_5837
    rfl (by decide +kernel) odd437_sorted_5684 odd437_sorted_5837

theorem odd437_queries_5838 : odd437Tree_5838.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_5838 [] [] 32311676421860 odd437Tree_5684 odd437Tree_5837
    rfl odd437_queries_5684 odd437_queries_5837

-- 77 source leaves.
theorem odd437_valid_5991 : odd437Tree_5991.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_5991 : odd437Tree_5991.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_5991 : odd437Tree_5991.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_6144 : odd437Tree_6144.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6144 : odd437Tree_6144.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6144 : odd437Tree_6144.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_6145 : odd437Tree_6145.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6145 [1] [12] 82346678648767 odd437Tree_5991 odd437Tree_6144
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5991 odd437_valid_6144

theorem odd437_sorted_6145 : odd437Tree_6145.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6145 [1] [12] 82346678648767 odd437Tree_5991 odd437Tree_6144
    rfl (by decide +kernel) odd437_sorted_5991 odd437_sorted_6144

theorem odd437_queries_6145 : odd437Tree_6145.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6145 [1] [12] 82346678648767 odd437Tree_5991 odd437Tree_6144
    rfl odd437_queries_5991 odd437_queries_6144

-- 308 source leaves.
theorem odd437_valid_6146 : odd437Tree_6146.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6146 [] [] 32311676421860 odd437Tree_5838 odd437Tree_6145
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5838 odd437_valid_6145

theorem odd437_sorted_6146 : odd437Tree_6146.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6146 [] [] 32311676421860 odd437Tree_5838 odd437Tree_6145
    rfl (by decide +kernel) odd437_sorted_5838 odd437_sorted_6145

theorem odd437_queries_6146 : odd437Tree_6146.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6146 [] [] 32311676421860 odd437Tree_5838 odd437Tree_6145
    rfl odd437_queries_5838 odd437_queries_6145

-- 615 source leaves.
theorem odd437_valid_6147 : odd437Tree_6147.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6147 [] [] 28031394617898 odd437Tree_5531 odd437Tree_6146
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_5531 odd437_valid_6146

theorem odd437_sorted_6147 : odd437Tree_6147.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6147 [] [] 28031394617898 odd437Tree_5531 odd437Tree_6146
    rfl (by decide +kernel) odd437_sorted_5531 odd437_sorted_6146

theorem odd437_queries_6147 : odd437Tree_6147.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6147 [] [] 28031394617898 odd437Tree_5531 odd437Tree_6146
    rfl odd437_queries_5531 odd437_queries_6146

-- 76 source leaves.
theorem odd437_valid_6298 : odd437Tree_6298.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6298 : odd437Tree_6298.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6298 : odd437Tree_6298.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_6451 : odd437Tree_6451.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6451 : odd437Tree_6451.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6451 : odd437Tree_6451.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_6452 : odd437Tree_6452.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6452 [1] [12] 82074309588742 odd437Tree_6298 odd437Tree_6451
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6298 odd437_valid_6451

theorem odd437_sorted_6452 : odd437Tree_6452.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6452 [1] [12] 82074309588742 odd437Tree_6298 odd437Tree_6451
    rfl (by decide +kernel) odd437_sorted_6298 odd437_sorted_6451

theorem odd437_queries_6452 : odd437Tree_6452.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6452 [1] [12] 82074309588742 odd437Tree_6298 odd437Tree_6451
    rfl odd437_queries_6298 odd437_queries_6451

-- 77 source leaves.
theorem odd437_valid_6605 : odd437Tree_6605.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6605 : odd437Tree_6605.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6605 : odd437Tree_6605.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_6758 : odd437Tree_6758.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6758 : odd437Tree_6758.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6758 : odd437Tree_6758.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_6759 : odd437Tree_6759.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6759 [1] [12] 82475120961383 odd437Tree_6605 odd437Tree_6758
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6605 odd437_valid_6758

theorem odd437_sorted_6759 : odd437Tree_6759.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6759 [1] [12] 82475120961383 odd437Tree_6605 odd437Tree_6758
    rfl (by decide +kernel) odd437_sorted_6605 odd437_sorted_6758

theorem odd437_queries_6759 : odd437Tree_6759.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6759 [1] [12] 82475120961383 odd437Tree_6605 odd437Tree_6758
    rfl odd437_queries_6605 odd437_queries_6758

-- 307 source leaves.
theorem odd437_valid_6760 : odd437Tree_6760.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_6760 [1] [12] 82074309588742 odd437Tree_6452 odd437Tree_6759
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6452 odd437_valid_6759

theorem odd437_sorted_6760 : odd437Tree_6760.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_6760 [1] [12] 82074309588742 odd437Tree_6452 odd437Tree_6759
    rfl (by decide +kernel) odd437_sorted_6452 odd437_sorted_6759

theorem odd437_queries_6760 : odd437Tree_6760.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_6760 [1] [12] 82074309588742 odd437Tree_6452 odd437Tree_6759
    rfl odd437_queries_6452 odd437_queries_6759

-- 77 source leaves.
theorem odd437_valid_6913 : odd437Tree_6913.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_6913 : odd437Tree_6913.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_6913 : odd437Tree_6913.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_7066 : odd437Tree_7066.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7066 : odd437Tree_7066.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7066 : odd437Tree_7066.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_7067 : odd437Tree_7067.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7067 [1] [12] 85865216920455 odd437Tree_6913 odd437Tree_7066
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6913 odd437_valid_7066

theorem odd437_sorted_7067 : odd437Tree_7067.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7067 [1] [12] 85865216920455 odd437Tree_6913 odd437Tree_7066
    rfl (by decide +kernel) odd437_sorted_6913 odd437_sorted_7066

theorem odd437_queries_7067 : odd437Tree_7067.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7067 [1] [12] 85865216920455 odd437Tree_6913 odd437Tree_7066
    rfl odd437_queries_6913 odd437_queries_7066

-- 77 source leaves.
theorem odd437_valid_7220 : odd437Tree_7220.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7220 : odd437Tree_7220.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7220 : odd437Tree_7220.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_7373 : odd437Tree_7373.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7373 : odd437Tree_7373.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7373 : odd437Tree_7373.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_7374 : odd437Tree_7374.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7374 [] [] 14377402511229 odd437Tree_7220 odd437Tree_7373
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7220 odd437_valid_7373

theorem odd437_sorted_7374 : odd437Tree_7374.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7374 [] [] 14377402511229 odd437Tree_7220 odd437Tree_7373
    rfl (by decide +kernel) odd437_sorted_7220 odd437_sorted_7373

theorem odd437_queries_7374 : odd437Tree_7374.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7374 [] [] 14377402511229 odd437Tree_7220 odd437Tree_7373
    rfl odd437_queries_7220 odd437_queries_7373

-- 308 source leaves.
theorem odd437_valid_7375 : odd437Tree_7375.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7375 [] [] 14377402511229 odd437Tree_7067 odd437Tree_7374
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7067 odd437_valid_7374

theorem odd437_sorted_7375 : odd437Tree_7375.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7375 [] [] 14377402511229 odd437Tree_7067 odd437Tree_7374
    rfl (by decide +kernel) odd437_sorted_7067 odd437_sorted_7374

theorem odd437_queries_7375 : odd437Tree_7375.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7375 [] [] 14377402511229 odd437Tree_7067 odd437Tree_7374
    rfl odd437_queries_7067 odd437_queries_7374

-- 615 source leaves.
theorem odd437_valid_7376 : odd437Tree_7376.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7376 [] [] 14377402511229 odd437Tree_6760 odd437Tree_7375
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6760 odd437_valid_7375

theorem odd437_sorted_7376 : odd437Tree_7376.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7376 [] [] 14377402511229 odd437Tree_6760 odd437Tree_7375
    rfl (by decide +kernel) odd437_sorted_6760 odd437_sorted_7375

theorem odd437_queries_7376 : odd437Tree_7376.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7376 [] [] 14377402511229 odd437Tree_6760 odd437Tree_7375
    rfl odd437_queries_6760 odd437_queries_7375

-- 1230 source leaves.
theorem odd437_valid_7377 : odd437Tree_7377.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7377 [] [] 14377402511229 odd437Tree_6147 odd437Tree_7376
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_6147 odd437_valid_7376

theorem odd437_sorted_7377 : odd437Tree_7377.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7377 [] [] 14377402511229 odd437Tree_6147 odd437Tree_7376
    rfl (by decide +kernel) odd437_sorted_6147 odd437_sorted_7376

theorem odd437_queries_7377 : odd437Tree_7377.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7377 [] [] 14377402511229 odd437Tree_6147 odd437Tree_7376
    rfl odd437_queries_6147 odd437_queries_7376

-- 76 source leaves.
theorem odd437_valid_7528 : odd437Tree_7528.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7528 : odd437Tree_7528.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7528 : odd437Tree_7528.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_7681 : odd437Tree_7681.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7681 : odd437Tree_7681.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7681 : odd437Tree_7681.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_7682 : odd437Tree_7682.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7682 [2] [6] 11500308615858 odd437Tree_7528 odd437Tree_7681
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7528 odd437_valid_7681

theorem odd437_sorted_7682 : odd437Tree_7682.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7682 [2] [6] 11500308615858 odd437Tree_7528 odd437Tree_7681
    rfl (by decide +kernel) odd437_sorted_7528 odd437_sorted_7681

theorem odd437_queries_7682 : odd437Tree_7682.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7682 [2] [6] 11500308615858 odd437Tree_7528 odd437Tree_7681
    rfl odd437_queries_7528 odd437_queries_7681

-- 77 source leaves.
theorem odd437_valid_7835 : odd437Tree_7835.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7835 : odd437Tree_7835.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7835 : odd437Tree_7835.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_7988 : odd437Tree_7988.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_7988 : odd437Tree_7988.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_7988 : odd437Tree_7988.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_7989 : odd437Tree_7989.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7989 [2] [6] 11911657517254 odd437Tree_7835 odd437Tree_7988
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7835 odd437_valid_7988

theorem odd437_sorted_7989 : odd437Tree_7989.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7989 [2] [6] 11911657517254 odd437Tree_7835 odd437Tree_7988
    rfl (by decide +kernel) odd437_sorted_7835 odd437_sorted_7988

theorem odd437_queries_7989 : odd437Tree_7989.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7989 [2] [6] 11911657517254 odd437Tree_7835 odd437Tree_7988
    rfl odd437_queries_7835 odd437_queries_7988

-- 307 source leaves.
theorem odd437_valid_7990 : odd437Tree_7990.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_7990 [2] [6] 11500308615858 odd437Tree_7682 odd437Tree_7989
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7682 odd437_valid_7989

theorem odd437_sorted_7990 : odd437Tree_7990.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_7990 [2] [6] 11500308615858 odd437Tree_7682 odd437Tree_7989
    rfl (by decide +kernel) odd437_sorted_7682 odd437_sorted_7989

theorem odd437_queries_7990 : odd437Tree_7990.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_7990 [2] [6] 11500308615858 odd437Tree_7682 odd437Tree_7989
    rfl odd437_queries_7682 odd437_queries_7989

-- 77 source leaves.
theorem odd437_valid_8143 : odd437Tree_8143.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8143 : odd437Tree_8143.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8143 : odd437Tree_8143.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_8296 : odd437Tree_8296.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8296 : odd437Tree_8296.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8296 : odd437Tree_8296.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_8297 : odd437Tree_8297.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_8297 [2] [6] 12460072376728 odd437Tree_8143 odd437Tree_8296
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8143 odd437_valid_8296

theorem odd437_sorted_8297 : odd437Tree_8297.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_8297 [2] [6] 12460072376728 odd437Tree_8143 odd437Tree_8296
    rfl (by decide +kernel) odd437_sorted_8143 odd437_sorted_8296

theorem odd437_queries_8297 : odd437Tree_8297.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_8297 [2] [6] 12460072376728 odd437Tree_8143 odd437Tree_8296
    rfl odd437_queries_8143 odd437_queries_8296

-- 77 source leaves.
theorem odd437_valid_8450 : odd437Tree_8450.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8450 : odd437Tree_8450.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8450 : odd437Tree_8450.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_8603 : odd437Tree_8603.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8603 : odd437Tree_8603.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8603 : odd437Tree_8603.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_8604 : odd437Tree_8604.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_8604 [2] [6] 16370029833423 odd437Tree_8450 odd437Tree_8603
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8450 odd437_valid_8603

theorem odd437_sorted_8604 : odd437Tree_8604.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_8604 [2] [6] 16370029833423 odd437Tree_8450 odd437Tree_8603
    rfl (by decide +kernel) odd437_sorted_8450 odd437_sorted_8603

theorem odd437_queries_8604 : odd437Tree_8604.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_8604 [2] [6] 16370029833423 odd437Tree_8450 odd437Tree_8603
    rfl odd437_queries_8450 odd437_queries_8603

-- 308 source leaves.
theorem odd437_valid_8605 : odd437Tree_8605.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_8605 [2] [6] 12460072376728 odd437Tree_8297 odd437Tree_8604
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8297 odd437_valid_8604

theorem odd437_sorted_8605 : odd437Tree_8605.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_8605 [2] [6] 12460072376728 odd437Tree_8297 odd437Tree_8604
    rfl (by decide +kernel) odd437_sorted_8297 odd437_sorted_8604

theorem odd437_queries_8605 : odd437Tree_8605.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_8605 [2] [6] 12460072376728 odd437Tree_8297 odd437Tree_8604
    rfl odd437_queries_8297 odd437_queries_8604

-- 615 source leaves.
theorem odd437_valid_8606 : odd437Tree_8606.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_8606 [2] [6] 11500308615858 odd437Tree_7990 odd437Tree_8605
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7990 odd437_valid_8605

theorem odd437_sorted_8606 : odd437Tree_8606.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_8606 [2] [6] 11500308615858 odd437Tree_7990 odd437Tree_8605
    rfl (by decide +kernel) odd437_sorted_7990 odd437_sorted_8605

theorem odd437_queries_8606 : odd437Tree_8606.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_8606 [2] [6] 11500308615858 odd437Tree_7990 odd437Tree_8605
    rfl odd437_queries_7990 odd437_queries_8605

-- 76 source leaves.
theorem odd437_valid_8757 : odd437Tree_8757.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8757 : odd437Tree_8757.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8757 : odd437Tree_8757.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_8910 : odd437Tree_8910.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_8910 : odd437Tree_8910.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_8910 : odd437Tree_8910.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_8911 : odd437Tree_8911.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_8911 [2] [] 17369401695086 odd437Tree_8757 odd437Tree_8910
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8757 odd437_valid_8910

theorem odd437_sorted_8911 : odd437Tree_8911.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_8911 [2] [] 17369401695086 odd437Tree_8757 odd437Tree_8910
    rfl (by decide +kernel) odd437_sorted_8757 odd437_sorted_8910

theorem odd437_queries_8911 : odd437Tree_8911.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_8911 [2] [] 17369401695086 odd437Tree_8757 odd437Tree_8910
    rfl odd437_queries_8757 odd437_queries_8910

-- 77 source leaves.
theorem odd437_valid_9064 : odd437Tree_9064.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9064 : odd437Tree_9064.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9064 : odd437Tree_9064.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_9217 : odd437Tree_9217.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9217 : odd437Tree_9217.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9217 : odd437Tree_9217.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_9218 : odd437Tree_9218.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9218 [2] [9] 71937638307441 odd437Tree_9064 odd437Tree_9217
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9064 odd437_valid_9217

theorem odd437_sorted_9218 : odd437Tree_9218.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9218 [2] [9] 71937638307441 odd437Tree_9064 odd437Tree_9217
    rfl (by decide +kernel) odd437_sorted_9064 odd437_sorted_9217

theorem odd437_queries_9218 : odd437Tree_9218.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9218 [2] [9] 71937638307441 odd437Tree_9064 odd437Tree_9217
    rfl odd437_queries_9064 odd437_queries_9217

-- 307 source leaves.
theorem odd437_valid_9219 : odd437Tree_9219.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9219 [2] [] 17369401695086 odd437Tree_8911 odd437Tree_9218
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8911 odd437_valid_9218

theorem odd437_sorted_9219 : odd437Tree_9219.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9219 [2] [] 17369401695086 odd437Tree_8911 odd437Tree_9218
    rfl (by decide +kernel) odd437_sorted_8911 odd437_sorted_9218

theorem odd437_queries_9219 : odd437Tree_9219.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9219 [2] [] 17369401695086 odd437Tree_8911 odd437Tree_9218
    rfl odd437_queries_8911 odd437_queries_9218

-- 77 source leaves.
theorem odd437_valid_9372 : odd437Tree_9372.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9372 : odd437Tree_9372.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9372 : odd437Tree_9372.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_9525 : odd437Tree_9525.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9525 : odd437Tree_9525.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9525 : odd437Tree_9525.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_9526 : odd437Tree_9526.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9526 [2] [9] 75448931502232 odd437Tree_9372 odd437Tree_9525
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9372 odd437_valid_9525

theorem odd437_sorted_9526 : odd437Tree_9526.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9526 [2] [9] 75448931502232 odd437Tree_9372 odd437Tree_9525
    rfl (by decide +kernel) odd437_sorted_9372 odd437_sorted_9525

theorem odd437_queries_9526 : odd437Tree_9526.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9526 [2] [9] 75448931502232 odd437Tree_9372 odd437Tree_9525
    rfl odd437_queries_9372 odd437_queries_9525

-- 77 source leaves.
theorem odd437_valid_9679 : odd437Tree_9679.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9679 : odd437Tree_9679.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9679 : odd437Tree_9679.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_9832 : odd437Tree_9832.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9832 : odd437Tree_9832.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9832 : odd437Tree_9832.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_9833 : odd437Tree_9833.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9833 [2] [9] 68229641645652 odd437Tree_9679 odd437Tree_9832
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9679 odd437_valid_9832

theorem odd437_sorted_9833 : odd437Tree_9833.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9833 [2] [9] 68229641645652 odd437Tree_9679 odd437Tree_9832
    rfl (by decide +kernel) odd437_sorted_9679 odd437_sorted_9832

theorem odd437_queries_9833 : odd437Tree_9833.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9833 [2] [9] 68229641645652 odd437Tree_9679 odd437Tree_9832
    rfl odd437_queries_9679 odd437_queries_9832

-- 308 source leaves.
theorem odd437_valid_9834 : odd437Tree_9834.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9834 [2] [9] 68229641645652 odd437Tree_9526 odd437Tree_9833
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9526 odd437_valid_9833

theorem odd437_sorted_9834 : odd437Tree_9834.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9834 [2] [9] 68229641645652 odd437Tree_9526 odd437Tree_9833
    rfl (by decide +kernel) odd437_sorted_9526 odd437_sorted_9833

theorem odd437_queries_9834 : odd437Tree_9834.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9834 [2] [9] 68229641645652 odd437Tree_9526 odd437Tree_9833
    rfl odd437_queries_9526 odd437_queries_9833

-- 615 source leaves.
theorem odd437_valid_9835 : odd437Tree_9835.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9835 [2] [] 17369401695086 odd437Tree_9219 odd437Tree_9834
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9219 odd437_valid_9834

theorem odd437_sorted_9835 : odd437Tree_9835.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9835 [2] [] 17369401695086 odd437Tree_9219 odd437Tree_9834
    rfl (by decide +kernel) odd437_sorted_9219 odd437_sorted_9834

theorem odd437_queries_9835 : odd437Tree_9835.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9835 [2] [] 17369401695086 odd437Tree_9219 odd437Tree_9834
    rfl odd437_queries_9219 odd437_queries_9834

-- 1230 source leaves.
theorem odd437_valid_9836 : odd437Tree_9836.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9836 [2] [] 11500308615858 odd437Tree_8606 odd437Tree_9835
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_8606 odd437_valid_9835

theorem odd437_sorted_9836 : odd437Tree_9836.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9836 [2] [] 11500308615858 odd437Tree_8606 odd437Tree_9835
    rfl (by decide +kernel) odd437_sorted_8606 odd437_sorted_9835

theorem odd437_queries_9836 : odd437Tree_9836.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9836 [2] [] 11500308615858 odd437Tree_8606 odd437Tree_9835
    rfl odd437_queries_8606 odd437_queries_9835

-- 2460 source leaves.
theorem odd437_valid_9837 : odd437Tree_9837.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9837 [] [] 11500308615858 odd437Tree_7377 odd437Tree_9836
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_7377 odd437_valid_9836

theorem odd437_sorted_9837 : odd437Tree_9837.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9837 [] [] 11500308615858 odd437Tree_7377 odd437Tree_9836
    rfl (by decide +kernel) odd437_sorted_7377 odd437_sorted_9836

theorem odd437_queries_9837 : odd437Tree_9837.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9837 [] [] 11500308615858 odd437Tree_7377 odd437Tree_9836
    rfl odd437_queries_7377 odd437_queries_9836

-- 4920 source leaves.
theorem odd437_valid_9838 : odd437Tree_9838.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_9838 [] [] 0 odd437Tree_4918 odd437Tree_9837
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_4918 odd437_valid_9837

theorem odd437_sorted_9838 : odd437Tree_9838.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_9838 [] [] 0 odd437Tree_4918 odd437Tree_9837
    rfl (by decide +kernel) odd437_sorted_4918 odd437_sorted_9837

theorem odd437_queries_9838 : odd437Tree_9838.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_9838 [] [] 0 odd437Tree_4918 odd437Tree_9837
    rfl odd437_queries_4918 odd437_queries_9837

-- 76 source leaves.
theorem odd437_valid_9989 : odd437Tree_9989.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_9989 : odd437Tree_9989.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_9989 : odd437Tree_9989.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_10142 : odd437Tree_10142.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10142 : odd437Tree_10142.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10142 : odd437Tree_10142.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_10143 : odd437Tree_10143.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_10143 [2] [9] 68229641340608 odd437Tree_9989 odd437Tree_10142
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9989 odd437_valid_10142

theorem odd437_sorted_10143 : odd437Tree_10143.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_10143 [2] [9] 68229641340608 odd437Tree_9989 odd437Tree_10142
    rfl (by decide +kernel) odd437_sorted_9989 odd437_sorted_10142

theorem odd437_queries_10143 : odd437Tree_10143.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_10143 [2] [9] 68229641340608 odd437Tree_9989 odd437Tree_10142
    rfl odd437_queries_9989 odd437_queries_10142

-- 77 source leaves.
theorem odd437_valid_10296 : odd437Tree_10296.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10296 : odd437Tree_10296.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10296 : odd437Tree_10296.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_10449 : odd437Tree_10449.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10449 : odd437Tree_10449.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10449 : odd437Tree_10449.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_10450 : odd437Tree_10450.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_10450 [2] [] 77674251345888 odd437Tree_10296 odd437Tree_10449
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10296 odd437_valid_10449

theorem odd437_sorted_10450 : odd437Tree_10450.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_10450 [2] [] 77674251345888 odd437Tree_10296 odd437Tree_10449
    rfl (by decide +kernel) odd437_sorted_10296 odd437_sorted_10449

theorem odd437_queries_10450 : odd437Tree_10450.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_10450 [2] [] 77674251345888 odd437Tree_10296 odd437Tree_10449
    rfl odd437_queries_10296 odd437_queries_10449

-- 307 source leaves.
theorem odd437_valid_10451 : odd437Tree_10451.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_10451 [2] [] 68229641340608 odd437Tree_10143 odd437Tree_10450
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10143 odd437_valid_10450

theorem odd437_sorted_10451 : odd437Tree_10451.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_10451 [2] [] 68229641340608 odd437Tree_10143 odd437Tree_10450
    rfl (by decide +kernel) odd437_sorted_10143 odd437_sorted_10450

theorem odd437_queries_10451 : odd437Tree_10451.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_10451 [2] [] 68229641340608 odd437Tree_10143 odd437Tree_10450
    rfl odd437_queries_10143 odd437_queries_10450

-- 77 source leaves.
theorem odd437_valid_10604 : odd437Tree_10604.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10604 : odd437Tree_10604.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10604 : odd437Tree_10604.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_10757 : odd437Tree_10757.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10757 : odd437Tree_10757.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10757 : odd437Tree_10757.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_10758 : odd437Tree_10758.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_10758 [2] [22] 80166138804800 odd437Tree_10604 odd437Tree_10757
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10604 odd437_valid_10757

theorem odd437_sorted_10758 : odd437Tree_10758.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_10758 [2] [22] 80166138804800 odd437Tree_10604 odd437Tree_10757
    rfl (by decide +kernel) odd437_sorted_10604 odd437_sorted_10757

theorem odd437_queries_10758 : odd437Tree_10758.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_10758 [2] [22] 80166138804800 odd437Tree_10604 odd437Tree_10757
    rfl odd437_queries_10604 odd437_queries_10757

-- 77 source leaves.
theorem odd437_valid_10911 : odd437Tree_10911.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_10911 : odd437Tree_10911.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_10911 : odd437Tree_10911.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_11064 : odd437Tree_11064.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11064 : odd437Tree_11064.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11064 : odd437Tree_11064.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_11065 : odd437Tree_11065.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11065 [2] [22] 80610532320663 odd437Tree_10911 odd437Tree_11064
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10911 odd437_valid_11064

theorem odd437_sorted_11065 : odd437Tree_11065.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11065 [2] [22] 80610532320663 odd437Tree_10911 odd437Tree_11064
    rfl (by decide +kernel) odd437_sorted_10911 odd437_sorted_11064

theorem odd437_queries_11065 : odd437Tree_11065.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11065 [2] [22] 80610532320663 odd437Tree_10911 odd437Tree_11064
    rfl odd437_queries_10911 odd437_queries_11064

-- 308 source leaves.
theorem odd437_valid_11066 : odd437Tree_11066.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11066 [2] [22] 80166138804800 odd437Tree_10758 odd437Tree_11065
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10758 odd437_valid_11065

theorem odd437_sorted_11066 : odd437Tree_11066.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11066 [2] [22] 80166138804800 odd437Tree_10758 odd437Tree_11065
    rfl (by decide +kernel) odd437_sorted_10758 odd437_sorted_11065

theorem odd437_queries_11066 : odd437Tree_11066.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11066 [2] [22] 80166138804800 odd437Tree_10758 odd437Tree_11065
    rfl odd437_queries_10758 odd437_queries_11065

-- 615 source leaves.
theorem odd437_valid_11067 : odd437Tree_11067.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11067 [2] [] 68229641340608 odd437Tree_10451 odd437Tree_11066
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_10451 odd437_valid_11066

theorem odd437_sorted_11067 : odd437Tree_11067.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11067 [2] [] 68229641340608 odd437Tree_10451 odd437Tree_11066
    rfl (by decide +kernel) odd437_sorted_10451 odd437_sorted_11066

theorem odd437_queries_11067 : odd437Tree_11067.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11067 [2] [] 68229641340608 odd437Tree_10451 odd437Tree_11066
    rfl odd437_queries_10451 odd437_queries_11066

-- 76 source leaves.
theorem odd437_valid_11218 : odd437Tree_11218.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11218 : odd437Tree_11218.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11218 : odd437Tree_11218.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_11371 : odd437Tree_11371.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11371 : odd437Tree_11371.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11371 : odd437Tree_11371.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_11372 : odd437Tree_11372.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11372 [2] [22] 80900105516725 odd437Tree_11218 odd437Tree_11371
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11218 odd437_valid_11371

theorem odd437_sorted_11372 : odd437Tree_11372.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11372 [2] [22] 80900105516725 odd437Tree_11218 odd437Tree_11371
    rfl (by decide +kernel) odd437_sorted_11218 odd437_sorted_11371

theorem odd437_queries_11372 : odd437Tree_11372.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11372 [2] [22] 80900105516725 odd437Tree_11218 odd437Tree_11371
    rfl odd437_queries_11218 odd437_queries_11371

-- 77 source leaves.
theorem odd437_valid_11525 : odd437Tree_11525.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11525 : odd437Tree_11525.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11525 : odd437Tree_11525.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_11678 : odd437Tree_11678.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11678 : odd437Tree_11678.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11678 : odd437Tree_11678.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_11679 : odd437Tree_11679.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11679 [] [] 4474941430036 odd437Tree_11525 odd437Tree_11678
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11525 odd437_valid_11678

theorem odd437_sorted_11679 : odd437Tree_11679.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11679 [] [] 4474941430036 odd437Tree_11525 odd437Tree_11678
    rfl (by decide +kernel) odd437_sorted_11525 odd437_sorted_11678

theorem odd437_queries_11679 : odd437Tree_11679.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11679 [] [] 4474941430036 odd437Tree_11525 odd437Tree_11678
    rfl odd437_queries_11525 odd437_queries_11678

-- 307 source leaves.
theorem odd437_valid_11680 : odd437Tree_11680.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11680 [] [] 4474941430036 odd437Tree_11372 odd437Tree_11679
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11372 odd437_valid_11679

theorem odd437_sorted_11680 : odd437Tree_11680.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11680 [] [] 4474941430036 odd437Tree_11372 odd437Tree_11679
    rfl (by decide +kernel) odd437_sorted_11372 odd437_sorted_11679

theorem odd437_queries_11680 : odd437Tree_11680.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11680 [] [] 4474941430036 odd437Tree_11372 odd437Tree_11679
    rfl odd437_queries_11372 odd437_queries_11679

-- 77 source leaves.
theorem odd437_valid_11833 : odd437Tree_11833.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11833 : odd437Tree_11833.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11833 : odd437Tree_11833.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_11986 : odd437Tree_11986.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_11986 : odd437Tree_11986.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_11986 : odd437Tree_11986.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_11987 : odd437Tree_11987.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_11987 [10] [6] 0 odd437Tree_11833 odd437Tree_11986
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11833 odd437_valid_11986

theorem odd437_sorted_11987 : odd437Tree_11987.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_11987 [10] [6] 0 odd437Tree_11833 odd437Tree_11986
    rfl (by decide +kernel) odd437_sorted_11833 odd437_sorted_11986

theorem odd437_queries_11987 : odd437Tree_11987.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_11987 [10] [6] 0 odd437Tree_11833 odd437Tree_11986
    rfl odd437_queries_11833 odd437_queries_11986

-- 77 source leaves.
theorem odd437_valid_12140 : odd437Tree_12140.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12140 : odd437Tree_12140.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12140 : odd437Tree_12140.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_12293 : odd437Tree_12293.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12293 : odd437Tree_12293.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12293 : odd437Tree_12293.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_12294 : odd437Tree_12294.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12294 [10] [6] 0 odd437Tree_12140 odd437Tree_12293
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12140 odd437_valid_12293

theorem odd437_sorted_12294 : odd437Tree_12294.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12294 [10] [6] 0 odd437Tree_12140 odd437Tree_12293
    rfl (by decide +kernel) odd437_sorted_12140 odd437_sorted_12293

theorem odd437_queries_12294 : odd437Tree_12294.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12294 [10] [6] 0 odd437Tree_12140 odd437Tree_12293
    rfl odd437_queries_12140 odd437_queries_12293

-- 308 source leaves.
theorem odd437_valid_12295 : odd437Tree_12295.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12295 [10] [6] 0 odd437Tree_11987 odd437Tree_12294
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11987 odd437_valid_12294

theorem odd437_sorted_12295 : odd437Tree_12295.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12295 [10] [6] 0 odd437Tree_11987 odd437Tree_12294
    rfl (by decide +kernel) odd437_sorted_11987 odd437_sorted_12294

theorem odd437_queries_12295 : odd437Tree_12295.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12295 [10] [6] 0 odd437Tree_11987 odd437Tree_12294
    rfl odd437_queries_11987 odd437_queries_12294

-- 615 source leaves.
theorem odd437_valid_12296 : odd437Tree_12296.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12296 [] [] 0 odd437Tree_11680 odd437Tree_12295
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11680 odd437_valid_12295

theorem odd437_sorted_12296 : odd437Tree_12296.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12296 [] [] 0 odd437Tree_11680 odd437Tree_12295
    rfl (by decide +kernel) odd437_sorted_11680 odd437_sorted_12295

theorem odd437_queries_12296 : odd437Tree_12296.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12296 [] [] 0 odd437Tree_11680 odd437Tree_12295
    rfl odd437_queries_11680 odd437_queries_12295

-- 1230 source leaves.
theorem odd437_valid_12297 : odd437Tree_12297.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12297 [] [] 0 odd437Tree_11067 odd437Tree_12296
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_11067 odd437_valid_12296

theorem odd437_sorted_12297 : odd437Tree_12297.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12297 [] [] 0 odd437Tree_11067 odd437Tree_12296
    rfl (by decide +kernel) odd437_sorted_11067 odd437_sorted_12296

theorem odd437_queries_12297 : odd437Tree_12297.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12297 [] [] 0 odd437Tree_11067 odd437Tree_12296
    rfl odd437_queries_11067 odd437_queries_12296

-- 76 source leaves.
theorem odd437_valid_12448 : odd437Tree_12448.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12448 : odd437Tree_12448.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12448 : odd437Tree_12448.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_12601 : odd437Tree_12601.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12601 : odd437Tree_12601.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12601 : odd437Tree_12601.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_12602 : odd437Tree_12602.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12602 [10] [6] 215324986682 odd437Tree_12448 odd437Tree_12601
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12448 odd437_valid_12601

theorem odd437_sorted_12602 : odd437Tree_12602.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12602 [10] [6] 215324986682 odd437Tree_12448 odd437Tree_12601
    rfl (by decide +kernel) odd437_sorted_12448 odd437_sorted_12601

theorem odd437_queries_12602 : odd437Tree_12602.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12602 [10] [6] 215324986682 odd437Tree_12448 odd437Tree_12601
    rfl odd437_queries_12448 odd437_queries_12601

-- 77 source leaves.
theorem odd437_valid_12755 : odd437Tree_12755.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12755 : odd437Tree_12755.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12755 : odd437Tree_12755.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_12908 : odd437Tree_12908.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_12908 : odd437Tree_12908.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_12908 : odd437Tree_12908.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_12909 : odd437Tree_12909.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12909 [10] [6] 2047976627350 odd437Tree_12755 odd437Tree_12908
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12755 odd437_valid_12908

theorem odd437_sorted_12909 : odd437Tree_12909.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12909 [10] [6] 2047976627350 odd437Tree_12755 odd437Tree_12908
    rfl (by decide +kernel) odd437_sorted_12755 odd437_sorted_12908

theorem odd437_queries_12909 : odd437Tree_12909.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12909 [10] [6] 2047976627350 odd437Tree_12755 odd437Tree_12908
    rfl odd437_queries_12755 odd437_queries_12908

-- 307 source leaves.
theorem odd437_valid_12910 : odd437Tree_12910.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_12910 [10] [6] 215324986682 odd437Tree_12602 odd437Tree_12909
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12602 odd437_valid_12909

theorem odd437_sorted_12910 : odd437Tree_12910.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_12910 [10] [6] 215324986682 odd437Tree_12602 odd437Tree_12909
    rfl (by decide +kernel) odd437_sorted_12602 odd437_sorted_12909

theorem odd437_queries_12910 : odd437Tree_12910.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_12910 [10] [6] 215324986682 odd437Tree_12602 odd437Tree_12909
    rfl odd437_queries_12602 odd437_queries_12909

-- 77 source leaves.
theorem odd437_valid_13063 : odd437Tree_13063.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13063 : odd437Tree_13063.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13063 : odd437Tree_13063.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_13216 : odd437Tree_13216.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13216 : odd437Tree_13216.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13216 : odd437Tree_13216.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_13217 : odd437Tree_13217.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_13217 [10] [] 2192619108779 odd437Tree_13063 odd437Tree_13216
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13063 odd437_valid_13216

theorem odd437_sorted_13217 : odd437Tree_13217.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_13217 [10] [] 2192619108779 odd437Tree_13063 odd437Tree_13216
    rfl (by decide +kernel) odd437_sorted_13063 odd437_sorted_13216

theorem odd437_queries_13217 : odd437Tree_13217.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_13217 [10] [] 2192619108779 odd437Tree_13063 odd437Tree_13216
    rfl odd437_queries_13063 odd437_queries_13216

-- 77 source leaves.
theorem odd437_valid_13370 : odd437Tree_13370.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13370 : odd437Tree_13370.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13370 : odd437Tree_13370.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_13523 : odd437Tree_13523.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13523 : odd437Tree_13523.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13523 : odd437Tree_13523.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_13524 : odd437Tree_13524.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_13524 [10] [9] 20047503547620 odd437Tree_13370 odd437Tree_13523
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13370 odd437_valid_13523

theorem odd437_sorted_13524 : odd437Tree_13524.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_13524 [10] [9] 20047503547620 odd437Tree_13370 odd437Tree_13523
    rfl (by decide +kernel) odd437_sorted_13370 odd437_sorted_13523

theorem odd437_queries_13524 : odd437Tree_13524.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_13524 [10] [9] 20047503547620 odd437Tree_13370 odd437Tree_13523
    rfl odd437_queries_13370 odd437_queries_13523

-- 308 source leaves.
theorem odd437_valid_13525 : odd437Tree_13525.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_13525 [10] [] 2192619108779 odd437Tree_13217 odd437Tree_13524
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13217 odd437_valid_13524

theorem odd437_sorted_13525 : odd437Tree_13525.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_13525 [10] [] 2192619108779 odd437Tree_13217 odd437Tree_13524
    rfl (by decide +kernel) odd437_sorted_13217 odd437_sorted_13524

theorem odd437_queries_13525 : odd437Tree_13525.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_13525 [10] [] 2192619108779 odd437Tree_13217 odd437Tree_13524
    rfl odd437_queries_13217 odd437_queries_13524

-- 615 source leaves.
theorem odd437_valid_13526 : odd437Tree_13526.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_13526 [10] [] 215324986682 odd437Tree_12910 odd437Tree_13525
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12910 odd437_valid_13525

theorem odd437_sorted_13526 : odd437Tree_13526.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_13526 [10] [] 215324986682 odd437Tree_12910 odd437Tree_13525
    rfl (by decide +kernel) odd437_sorted_12910 odd437_sorted_13525

theorem odd437_queries_13526 : odd437Tree_13526.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_13526 [10] [] 215324986682 odd437Tree_12910 odd437Tree_13525
    rfl odd437_queries_12910 odd437_queries_13525

-- 76 source leaves.
theorem odd437_valid_13677 : odd437Tree_13677.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13677 : odd437Tree_13677.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13677 : odd437Tree_13677.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_13830 : odd437Tree_13830.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13830 : odd437Tree_13830.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13830 : odd437Tree_13830.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_13831 : odd437Tree_13831.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_13831 [10] [9] 17577016682071 odd437Tree_13677 odd437Tree_13830
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13677 odd437_valid_13830

theorem odd437_sorted_13831 : odd437Tree_13831.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_13831 [10] [9] 17577016682071 odd437Tree_13677 odd437Tree_13830
    rfl (by decide +kernel) odd437_sorted_13677 odd437_sorted_13830

theorem odd437_queries_13831 : odd437Tree_13831.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_13831 [10] [9] 17577016682071 odd437Tree_13677 odd437Tree_13830
    rfl odd437_queries_13677 odd437_queries_13830

-- 77 source leaves.
theorem odd437_valid_13984 : odd437Tree_13984.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_13984 : odd437Tree_13984.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_13984 : odd437Tree_13984.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_14137 : odd437Tree_14137.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14137 : odd437Tree_14137.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14137 : odd437Tree_14137.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_14138 : odd437Tree_14138.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14138 [10] [9] 19490005748935 odd437Tree_13984 odd437Tree_14137
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13984 odd437_valid_14137

theorem odd437_sorted_14138 : odd437Tree_14138.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14138 [10] [9] 19490005748935 odd437Tree_13984 odd437Tree_14137
    rfl (by decide +kernel) odd437_sorted_13984 odd437_sorted_14137

theorem odd437_queries_14138 : odd437Tree_14138.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14138 [10] [9] 19490005748935 odd437Tree_13984 odd437Tree_14137
    rfl odd437_queries_13984 odd437_queries_14137

-- 307 source leaves.
theorem odd437_valid_14139 : odd437Tree_14139.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14139 [10] [9] 17577016682071 odd437Tree_13831 odd437Tree_14138
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13831 odd437_valid_14138

theorem odd437_sorted_14139 : odd437Tree_14139.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14139 [10] [9] 17577016682071 odd437Tree_13831 odd437Tree_14138
    rfl (by decide +kernel) odd437_sorted_13831 odd437_sorted_14138

theorem odd437_queries_14139 : odd437Tree_14139.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14139 [10] [9] 17577016682071 odd437Tree_13831 odd437Tree_14138
    rfl odd437_queries_13831 odd437_queries_14138

-- 77 source leaves.
theorem odd437_valid_14292 : odd437Tree_14292.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14292 : odd437Tree_14292.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14292 : odd437Tree_14292.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_14445 : odd437Tree_14445.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14445 : odd437Tree_14445.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14445 : odd437Tree_14445.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_14446 : odd437Tree_14446.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14446 [10] [9] 26614018616129 odd437Tree_14292 odd437Tree_14445
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14292 odd437_valid_14445

theorem odd437_sorted_14446 : odd437Tree_14446.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14446 [10] [9] 26614018616129 odd437Tree_14292 odd437Tree_14445
    rfl (by decide +kernel) odd437_sorted_14292 odd437_sorted_14445

theorem odd437_queries_14446 : odd437Tree_14446.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14446 [10] [9] 26614018616129 odd437Tree_14292 odd437Tree_14445
    rfl odd437_queries_14292 odd437_queries_14445

-- 77 source leaves.
theorem odd437_valid_14599 : odd437Tree_14599.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14599 : odd437Tree_14599.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14599 : odd437Tree_14599.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_14752 : odd437Tree_14752.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14752 : odd437Tree_14752.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14752 : odd437Tree_14752.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_14753 : odd437Tree_14753.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14753 [10] [] 4998201573179 odd437Tree_14599 odd437Tree_14752
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14599 odd437_valid_14752

theorem odd437_sorted_14753 : odd437Tree_14753.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14753 [10] [] 4998201573179 odd437Tree_14599 odd437Tree_14752
    rfl (by decide +kernel) odd437_sorted_14599 odd437_sorted_14752

theorem odd437_queries_14753 : odd437Tree_14753.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14753 [10] [] 4998201573179 odd437Tree_14599 odd437Tree_14752
    rfl odd437_queries_14599 odd437_queries_14752

-- 308 source leaves.
theorem odd437_valid_14754 : odd437Tree_14754.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14754 [10] [] 4998201573179 odd437Tree_14446 odd437Tree_14753
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14446 odd437_valid_14753

theorem odd437_sorted_14754 : odd437Tree_14754.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14754 [10] [] 4998201573179 odd437Tree_14446 odd437Tree_14753
    rfl (by decide +kernel) odd437_sorted_14446 odd437_sorted_14753

theorem odd437_queries_14754 : odd437Tree_14754.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14754 [10] [] 4998201573179 odd437Tree_14446 odd437Tree_14753
    rfl odd437_queries_14446 odd437_queries_14753

-- 615 source leaves.
theorem odd437_valid_14755 : odd437Tree_14755.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14755 [10] [] 4998201573179 odd437Tree_14139 odd437Tree_14754
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14139 odd437_valid_14754

theorem odd437_sorted_14755 : odd437Tree_14755.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14755 [10] [] 4998201573179 odd437Tree_14139 odd437Tree_14754
    rfl (by decide +kernel) odd437_sorted_14139 odd437_sorted_14754

theorem odd437_queries_14755 : odd437Tree_14755.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14755 [10] [] 4998201573179 odd437Tree_14139 odd437Tree_14754
    rfl odd437_queries_14139 odd437_queries_14754

-- 1230 source leaves.
theorem odd437_valid_14756 : odd437Tree_14756.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14756 [10] [] 215324986682 odd437Tree_13526 odd437Tree_14755
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_13526 odd437_valid_14755

theorem odd437_sorted_14756 : odd437Tree_14756.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14756 [10] [] 215324986682 odd437Tree_13526 odd437Tree_14755
    rfl (by decide +kernel) odd437_sorted_13526 odd437_sorted_14755

theorem odd437_queries_14756 : odd437Tree_14756.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14756 [10] [] 215324986682 odd437Tree_13526 odd437Tree_14755
    rfl odd437_queries_13526 odd437_queries_14755

-- 2460 source leaves.
theorem odd437_valid_14757 : odd437Tree_14757.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_14757 [] [] 0 odd437Tree_12297 odd437Tree_14756
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_12297 odd437_valid_14756

theorem odd437_sorted_14757 : odd437Tree_14757.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_14757 [] [] 0 odd437Tree_12297 odd437Tree_14756
    rfl (by decide +kernel) odd437_sorted_12297 odd437_sorted_14756

theorem odd437_queries_14757 : odd437Tree_14757.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_14757 [] [] 0 odd437Tree_12297 odd437Tree_14756
    rfl odd437_queries_12297 odd437_queries_14756

-- 76 source leaves.
theorem odd437_valid_14908 : odd437Tree_14908.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_14908 : odd437Tree_14908.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_14908 : odd437Tree_14908.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_15061 : odd437Tree_15061.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15061 : odd437Tree_15061.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15061 : odd437Tree_15061.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_15062 : odd437Tree_15062.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15062 [10] [19] 4460964068858 odd437Tree_14908 odd437Tree_15061
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14908 odd437_valid_15061

theorem odd437_sorted_15062 : odd437Tree_15062.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15062 [10] [19] 4460964068858 odd437Tree_14908 odd437Tree_15061
    rfl (by decide +kernel) odd437_sorted_14908 odd437_sorted_15061

theorem odd437_queries_15062 : odd437Tree_15062.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15062 [10] [19] 4460964068858 odd437Tree_14908 odd437Tree_15061
    rfl odd437_queries_14908 odd437_queries_15061

-- 77 source leaves.
theorem odd437_valid_15215 : odd437Tree_15215.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15215 : odd437Tree_15215.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15215 : odd437Tree_15215.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_15368 : odd437Tree_15368.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15368 : odd437Tree_15368.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15368 : odd437Tree_15368.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_15369 : odd437Tree_15369.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15369 [10] [19] 4945170558944 odd437Tree_15215 odd437Tree_15368
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15215 odd437_valid_15368

theorem odd437_sorted_15369 : odd437Tree_15369.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15369 [10] [19] 4945170558944 odd437Tree_15215 odd437Tree_15368
    rfl (by decide +kernel) odd437_sorted_15215 odd437_sorted_15368

theorem odd437_queries_15369 : odd437Tree_15369.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15369 [10] [19] 4945170558944 odd437Tree_15215 odd437Tree_15368
    rfl odd437_queries_15215 odd437_queries_15368

-- 307 source leaves.
theorem odd437_valid_15370 : odd437Tree_15370.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15370 [10] [19] 4460964068858 odd437Tree_15062 odd437Tree_15369
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15062 odd437_valid_15369

theorem odd437_sorted_15370 : odd437Tree_15370.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15370 [10] [19] 4460964068858 odd437Tree_15062 odd437Tree_15369
    rfl (by decide +kernel) odd437_sorted_15062 odd437_sorted_15369

theorem odd437_queries_15370 : odd437Tree_15370.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15370 [10] [19] 4460964068858 odd437Tree_15062 odd437Tree_15369
    rfl odd437_queries_15062 odd437_queries_15369

-- 77 source leaves.
theorem odd437_valid_15523 : odd437Tree_15523.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15523 : odd437Tree_15523.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15523 : odd437Tree_15523.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_15676 : odd437Tree_15676.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15676 : odd437Tree_15676.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15676 : odd437Tree_15676.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_15677 : odd437Tree_15677.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15677 [10] [19] 5230801041111 odd437Tree_15523 odd437Tree_15676
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15523 odd437_valid_15676

theorem odd437_sorted_15677 : odd437Tree_15677.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15677 [10] [19] 5230801041111 odd437Tree_15523 odd437Tree_15676
    rfl (by decide +kernel) odd437_sorted_15523 odd437_sorted_15676

theorem odd437_queries_15677 : odd437Tree_15677.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15677 [10] [19] 5230801041111 odd437Tree_15523 odd437Tree_15676
    rfl odd437_queries_15523 odd437_queries_15676

-- 77 source leaves.
theorem odd437_valid_15830 : odd437Tree_15830.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15830 : odd437Tree_15830.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15830 : odd437Tree_15830.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_15983 : odd437Tree_15983.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_15983 : odd437Tree_15983.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_15983 : odd437Tree_15983.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_15984 : odd437Tree_15984.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15984 [10] [19] 11138433082102 odd437Tree_15830 odd437Tree_15983
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15830 odd437_valid_15983

theorem odd437_sorted_15984 : odd437Tree_15984.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15984 [10] [19] 11138433082102 odd437Tree_15830 odd437Tree_15983
    rfl (by decide +kernel) odd437_sorted_15830 odd437_sorted_15983

theorem odd437_queries_15984 : odd437Tree_15984.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15984 [10] [19] 11138433082102 odd437Tree_15830 odd437Tree_15983
    rfl odd437_queries_15830 odd437_queries_15983

-- 308 source leaves.
theorem odd437_valid_15985 : odd437Tree_15985.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15985 [10] [19] 5230801041111 odd437Tree_15677 odd437Tree_15984
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15677 odd437_valid_15984

theorem odd437_sorted_15985 : odd437Tree_15985.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15985 [10] [19] 5230801041111 odd437Tree_15677 odd437Tree_15984
    rfl (by decide +kernel) odd437_sorted_15677 odd437_sorted_15984

theorem odd437_queries_15985 : odd437Tree_15985.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15985 [10] [19] 5230801041111 odd437Tree_15677 odd437Tree_15984
    rfl odd437_queries_15677 odd437_queries_15984

-- 615 source leaves.
theorem odd437_valid_15986 : odd437Tree_15986.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_15986 [10] [19] 4460964068858 odd437Tree_15370 odd437Tree_15985
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15370 odd437_valid_15985

theorem odd437_sorted_15986 : odd437Tree_15986.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_15986 [10] [19] 4460964068858 odd437Tree_15370 odd437Tree_15985
    rfl (by decide +kernel) odd437_sorted_15370 odd437_sorted_15985

theorem odd437_queries_15986 : odd437Tree_15986.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_15986 [10] [19] 4460964068858 odd437Tree_15370 odd437Tree_15985
    rfl odd437_queries_15370 odd437_queries_15985

-- 76 source leaves.
theorem odd437_valid_16137 : odd437Tree_16137.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16137 : odd437Tree_16137.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16137 : odd437Tree_16137.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_16290 : odd437Tree_16290.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16290 : odd437Tree_16290.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16290 : odd437Tree_16290.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_16291 : odd437Tree_16291.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_16291 [10] [] 13694088839981 odd437Tree_16137 odd437Tree_16290
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16137 odd437_valid_16290

theorem odd437_sorted_16291 : odd437Tree_16291.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_16291 [10] [] 13694088839981 odd437Tree_16137 odd437Tree_16290
    rfl (by decide +kernel) odd437_sorted_16137 odd437_sorted_16290

theorem odd437_queries_16291 : odd437Tree_16291.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_16291 [10] [] 13694088839981 odd437Tree_16137 odd437Tree_16290
    rfl odd437_queries_16137 odd437_queries_16290

-- 77 source leaves.
theorem odd437_valid_16444 : odd437Tree_16444.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16444 : odd437Tree_16444.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16444 : odd437Tree_16444.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_16597 : odd437Tree_16597.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16597 : odd437Tree_16597.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16597 : odd437Tree_16597.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_16598 : odd437Tree_16598.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_16598 [10] [22] 35407297345275 odd437Tree_16444 odd437Tree_16597
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16444 odd437_valid_16597

theorem odd437_sorted_16598 : odd437Tree_16598.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_16598 [10] [22] 35407297345275 odd437Tree_16444 odd437Tree_16597
    rfl (by decide +kernel) odd437_sorted_16444 odd437_sorted_16597

theorem odd437_queries_16598 : odd437Tree_16598.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_16598 [10] [22] 35407297345275 odd437Tree_16444 odd437Tree_16597
    rfl odd437_queries_16444 odd437_queries_16597

-- 307 source leaves.
theorem odd437_valid_16599 : odd437Tree_16599.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_16599 [10] [] 13694088839981 odd437Tree_16291 odd437Tree_16598
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16291 odd437_valid_16598

theorem odd437_sorted_16599 : odd437Tree_16599.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_16599 [10] [] 13694088839981 odd437Tree_16291 odd437Tree_16598
    rfl (by decide +kernel) odd437_sorted_16291 odd437_sorted_16598

theorem odd437_queries_16599 : odd437Tree_16599.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_16599 [10] [] 13694088839981 odd437Tree_16291 odd437Tree_16598
    rfl odd437_queries_16291 odd437_queries_16598

-- 77 source leaves.
theorem odd437_valid_16752 : odd437Tree_16752.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16752 : odd437Tree_16752.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16752 : odd437Tree_16752.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_16905 : odd437Tree_16905.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_16905 : odd437Tree_16905.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_16905 : odd437Tree_16905.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_16906 : odd437Tree_16906.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_16906 [10] [22] 36668935640505 odd437Tree_16752 odd437Tree_16905
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16752 odd437_valid_16905

theorem odd437_sorted_16906 : odd437Tree_16906.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_16906 [10] [22] 36668935640505 odd437Tree_16752 odd437Tree_16905
    rfl (by decide +kernel) odd437_sorted_16752 odd437_sorted_16905

theorem odd437_queries_16906 : odd437Tree_16906.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_16906 [10] [22] 36668935640505 odd437Tree_16752 odd437Tree_16905
    rfl odd437_queries_16752 odd437_queries_16905

-- 77 source leaves.
theorem odd437_valid_17059 : odd437Tree_17059.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17059 : odd437Tree_17059.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17059 : odd437Tree_17059.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_17212 : odd437Tree_17212.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17212 : odd437Tree_17212.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17212 : odd437Tree_17212.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_17213 : odd437Tree_17213.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17213 [10] [22] 37737505073455 odd437Tree_17059 odd437Tree_17212
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17059 odd437_valid_17212

theorem odd437_sorted_17213 : odd437Tree_17213.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17213 [10] [22] 37737505073455 odd437Tree_17059 odd437Tree_17212
    rfl (by decide +kernel) odd437_sorted_17059 odd437_sorted_17212

theorem odd437_queries_17213 : odd437Tree_17213.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17213 [10] [22] 37737505073455 odd437Tree_17059 odd437Tree_17212
    rfl odd437_queries_17059 odd437_queries_17212

-- 308 source leaves.
theorem odd437_valid_17214 : odd437Tree_17214.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17214 [10] [22] 36668935640505 odd437Tree_16906 odd437Tree_17213
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16906 odd437_valid_17213

theorem odd437_sorted_17214 : odd437Tree_17214.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17214 [10] [22] 36668935640505 odd437Tree_16906 odd437Tree_17213
    rfl (by decide +kernel) odd437_sorted_16906 odd437_sorted_17213

theorem odd437_queries_17214 : odd437Tree_17214.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17214 [10] [22] 36668935640505 odd437Tree_16906 odd437Tree_17213
    rfl odd437_queries_16906 odd437_queries_17213

-- 615 source leaves.
theorem odd437_valid_17215 : odd437Tree_17215.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17215 [10] [] 13694088839981 odd437Tree_16599 odd437Tree_17214
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_16599 odd437_valid_17214

theorem odd437_sorted_17215 : odd437Tree_17215.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17215 [10] [] 13694088839981 odd437Tree_16599 odd437Tree_17214
    rfl (by decide +kernel) odd437_sorted_16599 odd437_sorted_17214

theorem odd437_queries_17215 : odd437Tree_17215.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17215 [10] [] 13694088839981 odd437Tree_16599 odd437Tree_17214
    rfl odd437_queries_16599 odd437_queries_17214

-- 1230 source leaves.
theorem odd437_valid_17216 : odd437Tree_17216.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17216 [10] [] 4460964068858 odd437Tree_15986 odd437Tree_17215
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_15986 odd437_valid_17215

theorem odd437_sorted_17216 : odd437Tree_17216.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17216 [10] [] 4460964068858 odd437Tree_15986 odd437Tree_17215
    rfl (by decide +kernel) odd437_sorted_15986 odd437_sorted_17215

theorem odd437_queries_17216 : odd437Tree_17216.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17216 [10] [] 4460964068858 odd437Tree_15986 odd437Tree_17215
    rfl odd437_queries_15986 odd437_queries_17215

-- 76 source leaves.
theorem odd437_valid_17367 : odd437Tree_17367.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17367 : odd437Tree_17367.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17367 : odd437Tree_17367.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_17520 : odd437Tree_17520.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17520 : odd437Tree_17520.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17520 : odd437Tree_17520.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_17521 : odd437Tree_17521.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17521 [] [] 46338277473284 odd437Tree_17367 odd437Tree_17520
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17367 odd437_valid_17520

theorem odd437_sorted_17521 : odd437Tree_17521.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17521 [] [] 46338277473284 odd437Tree_17367 odd437Tree_17520
    rfl (by decide +kernel) odd437_sorted_17367 odd437_sorted_17520

theorem odd437_queries_17521 : odd437Tree_17521.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17521 [] [] 46338277473284 odd437Tree_17367 odd437Tree_17520
    rfl odd437_queries_17367 odd437_queries_17520

-- 77 source leaves.
theorem odd437_valid_17674 : odd437Tree_17674.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17674 : odd437Tree_17674.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17674 : odd437Tree_17674.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_17827 : odd437Tree_17827.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17827 : odd437Tree_17827.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17827 : odd437Tree_17827.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_17828 : odd437Tree_17828.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17828 [11] [5] 93588348469470 odd437Tree_17674 odd437Tree_17827
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17674 odd437_valid_17827

theorem odd437_sorted_17828 : odd437Tree_17828.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17828 [11] [5] 93588348469470 odd437Tree_17674 odd437Tree_17827
    rfl (by decide +kernel) odd437_sorted_17674 odd437_sorted_17827

theorem odd437_queries_17828 : odd437Tree_17828.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17828 [11] [5] 93588348469470 odd437Tree_17674 odd437Tree_17827
    rfl odd437_queries_17674 odd437_queries_17827

-- 307 source leaves.
theorem odd437_valid_17829 : odd437Tree_17829.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_17829 [] [] 46338277473284 odd437Tree_17521 odd437Tree_17828
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17521 odd437_valid_17828

theorem odd437_sorted_17829 : odd437Tree_17829.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_17829 [] [] 46338277473284 odd437Tree_17521 odd437Tree_17828
    rfl (by decide +kernel) odd437_sorted_17521 odd437_sorted_17828

theorem odd437_queries_17829 : odd437Tree_17829.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_17829 [] [] 46338277473284 odd437Tree_17521 odd437Tree_17828
    rfl odd437_queries_17521 odd437_queries_17828

-- 77 source leaves.
theorem odd437_valid_17982 : odd437Tree_17982.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_17982 : odd437Tree_17982.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_17982 : odd437Tree_17982.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_18135 : odd437Tree_18135.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18135 : odd437Tree_18135.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18135 : odd437Tree_18135.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_18136 : odd437Tree_18136.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_18136 [11] [5] 91465030878467 odd437Tree_17982 odd437Tree_18135
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17982 odd437_valid_18135

theorem odd437_sorted_18136 : odd437Tree_18136.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_18136 [11] [5] 91465030878467 odd437Tree_17982 odd437Tree_18135
    rfl (by decide +kernel) odd437_sorted_17982 odd437_sorted_18135

theorem odd437_queries_18136 : odd437Tree_18136.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_18136 [11] [5] 91465030878467 odd437Tree_17982 odd437Tree_18135
    rfl odd437_queries_17982 odd437_queries_18135

-- 77 source leaves.
theorem odd437_valid_18289 : odd437Tree_18289.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18289 : odd437Tree_18289.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18289 : odd437Tree_18289.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_18442 : odd437Tree_18442.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18442 : odd437Tree_18442.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18442 : odd437Tree_18442.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_18443 : odd437Tree_18443.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_18443 [11] [5] 92474832652703 odd437Tree_18289 odd437Tree_18442
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18289 odd437_valid_18442

theorem odd437_sorted_18443 : odd437Tree_18443.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_18443 [11] [5] 92474832652703 odd437Tree_18289 odd437Tree_18442
    rfl (by decide +kernel) odd437_sorted_18289 odd437_sorted_18442

theorem odd437_queries_18443 : odd437Tree_18443.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_18443 [11] [5] 92474832652703 odd437Tree_18289 odd437Tree_18442
    rfl odd437_queries_18289 odd437_queries_18442

-- 308 source leaves.
theorem odd437_valid_18444 : odd437Tree_18444.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_18444 [11] [5] 91465030878467 odd437Tree_18136 odd437Tree_18443
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18136 odd437_valid_18443

theorem odd437_sorted_18444 : odd437Tree_18444.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_18444 [11] [5] 91465030878467 odd437Tree_18136 odd437Tree_18443
    rfl (by decide +kernel) odd437_sorted_18136 odd437_sorted_18443

theorem odd437_queries_18444 : odd437Tree_18444.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_18444 [11] [5] 91465030878467 odd437Tree_18136 odd437Tree_18443
    rfl odd437_queries_18136 odd437_queries_18443

-- 615 source leaves.
theorem odd437_valid_18445 : odd437Tree_18445.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_18445 [] [] 46338277473284 odd437Tree_17829 odd437Tree_18444
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17829 odd437_valid_18444

theorem odd437_sorted_18445 : odd437Tree_18445.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_18445 [] [] 46338277473284 odd437Tree_17829 odd437Tree_18444
    rfl (by decide +kernel) odd437_sorted_17829 odd437_sorted_18444

theorem odd437_queries_18445 : odd437Tree_18445.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_18445 [] [] 46338277473284 odd437Tree_17829 odd437Tree_18444
    rfl odd437_queries_17829 odd437_queries_18444

-- 77 source leaves.
theorem odd437_valid_18598 : odd437Tree_18598.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18598 : odd437Tree_18598.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18598 : odd437Tree_18598.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_18751 : odd437Tree_18751.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18751 : odd437Tree_18751.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18751 : odd437Tree_18751.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_18752 : odd437Tree_18752.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_18752 [11] [5] 92601861267768 odd437Tree_18598 odd437Tree_18751
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18598 odd437_valid_18751

theorem odd437_sorted_18752 : odd437Tree_18752.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_18752 [11] [5] 92601861267768 odd437Tree_18598 odd437Tree_18751
    rfl (by decide +kernel) odd437_sorted_18598 odd437_sorted_18751

theorem odd437_queries_18752 : odd437Tree_18752.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_18752 [11] [5] 92601861267768 odd437Tree_18598 odd437Tree_18751
    rfl odd437_queries_18598 odd437_queries_18751

-- 77 source leaves.
theorem odd437_valid_18905 : odd437Tree_18905.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_18905 : odd437Tree_18905.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_18905 : odd437Tree_18905.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_19058 : odd437Tree_19058.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19058 : odd437Tree_19058.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19058 : odd437Tree_19058.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_19059 : odd437Tree_19059.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19059 [11] [] 15666489335468 odd437Tree_18905 odd437Tree_19058
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18905 odd437_valid_19058

theorem odd437_sorted_19059 : odd437Tree_19059.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19059 [11] [] 15666489335468 odd437Tree_18905 odd437Tree_19058
    rfl (by decide +kernel) odd437_sorted_18905 odd437_sorted_19058

theorem odd437_queries_19059 : odd437Tree_19059.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19059 [11] [] 15666489335468 odd437Tree_18905 odd437Tree_19058
    rfl odd437_queries_18905 odd437_queries_19058

-- 308 source leaves.
theorem odd437_valid_19060 : odd437Tree_19060.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19060 [11] [] 15666489335468 odd437Tree_18752 odd437Tree_19059
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18752 odd437_valid_19059

theorem odd437_sorted_19060 : odd437Tree_19060.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19060 [11] [] 15666489335468 odd437Tree_18752 odd437Tree_19059
    rfl (by decide +kernel) odd437_sorted_18752 odd437_sorted_19059

theorem odd437_queries_19060 : odd437Tree_19060.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19060 [11] [] 15666489335468 odd437Tree_18752 odd437Tree_19059
    rfl odd437_queries_18752 odd437_queries_19059

-- 77 source leaves.
theorem odd437_valid_19213 : odd437Tree_19213.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19213 : odd437Tree_19213.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19213 : odd437Tree_19213.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_19366 : odd437Tree_19366.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19366 : odd437Tree_19366.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19366 : odd437Tree_19366.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_19367 : odd437Tree_19367.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19367 [11] [16] 13307306609852 odd437Tree_19213 odd437Tree_19366
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19213 odd437_valid_19366

theorem odd437_sorted_19367 : odd437Tree_19367.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19367 [11] [16] 13307306609852 odd437Tree_19213 odd437Tree_19366
    rfl (by decide +kernel) odd437_sorted_19213 odd437_sorted_19366

theorem odd437_queries_19367 : odd437Tree_19367.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19367 [11] [16] 13307306609852 odd437Tree_19213 odd437Tree_19366
    rfl odd437_queries_19213 odd437_queries_19366

-- 77 source leaves.
theorem odd437_valid_19520 : odd437Tree_19520.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19520 : odd437Tree_19520.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19520 : odd437Tree_19520.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_19673 : odd437Tree_19673.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19673 : odd437Tree_19673.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19673 : odd437Tree_19673.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_19674 : odd437Tree_19674.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19674 [11] [16] 8559954543354 odd437Tree_19520 odd437Tree_19673
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19520 odd437_valid_19673

theorem odd437_sorted_19674 : odd437Tree_19674.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19674 [11] [16] 8559954543354 odd437Tree_19520 odd437Tree_19673
    rfl (by decide +kernel) odd437_sorted_19520 odd437_sorted_19673

theorem odd437_queries_19674 : odd437Tree_19674.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19674 [11] [16] 8559954543354 odd437Tree_19520 odd437Tree_19673
    rfl odd437_queries_19520 odd437_queries_19673

-- 308 source leaves.
theorem odd437_valid_19675 : odd437Tree_19675.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19675 [11] [16] 8559954543354 odd437Tree_19367 odd437Tree_19674
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19367 odd437_valid_19674

theorem odd437_sorted_19675 : odd437Tree_19675.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19675 [11] [16] 8559954543354 odd437Tree_19367 odd437Tree_19674
    rfl (by decide +kernel) odd437_sorted_19367 odd437_sorted_19674

theorem odd437_queries_19675 : odd437Tree_19675.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19675 [11] [16] 8559954543354 odd437Tree_19367 odd437Tree_19674
    rfl odd437_queries_19367 odd437_queries_19674

-- 616 source leaves.
theorem odd437_valid_19676 : odd437Tree_19676.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19676 [11] [] 8559954543354 odd437Tree_19060 odd437Tree_19675
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19060 odd437_valid_19675

theorem odd437_sorted_19676 : odd437Tree_19676.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19676 [11] [] 8559954543354 odd437Tree_19060 odd437Tree_19675
    rfl (by decide +kernel) odd437_sorted_19060 odd437_sorted_19675

theorem odd437_queries_19676 : odd437Tree_19676.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19676 [11] [] 8559954543354 odd437Tree_19060 odd437Tree_19675
    rfl odd437_queries_19060 odd437_queries_19675

-- 1231 source leaves.
theorem odd437_valid_19677 : odd437Tree_19677.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19677 [] [] 8559954543354 odd437Tree_18445 odd437Tree_19676
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_18445 odd437_valid_19676

theorem odd437_sorted_19677 : odd437Tree_19677.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19677 [] [] 8559954543354 odd437Tree_18445 odd437Tree_19676
    rfl (by decide +kernel) odd437_sorted_18445 odd437_sorted_19676

theorem odd437_queries_19677 : odd437Tree_19677.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19677 [] [] 8559954543354 odd437Tree_18445 odd437Tree_19676
    rfl odd437_queries_18445 odd437_queries_19676

-- 2461 source leaves.
theorem odd437_valid_19678 : odd437Tree_19678.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19678 [] [] 4460964068858 odd437Tree_17216 odd437Tree_19677
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_17216 odd437_valid_19677

theorem odd437_sorted_19678 : odd437Tree_19678.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19678 [] [] 4460964068858 odd437Tree_17216 odd437Tree_19677
    rfl (by decide +kernel) odd437_sorted_17216 odd437_sorted_19677

theorem odd437_queries_19678 : odd437Tree_19678.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19678 [] [] 4460964068858 odd437Tree_17216 odd437Tree_19677
    rfl odd437_queries_17216 odd437_queries_19677

-- 4921 source leaves.
theorem odd437_valid_19679 : odd437Tree_19679.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19679 [] [] 0 odd437Tree_14757 odd437Tree_19678
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_14757 odd437_valid_19678

theorem odd437_sorted_19679 : odd437Tree_19679.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19679 [] [] 0 odd437Tree_14757 odd437Tree_19678
    rfl (by decide +kernel) odd437_sorted_14757 odd437_sorted_19678

theorem odd437_queries_19679 : odd437Tree_19679.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19679 [] [] 0 odd437Tree_14757 odd437Tree_19678
    rfl odd437_queries_14757 odd437_queries_19678

-- 9841 source leaves.
theorem odd437_valid_19680 : odd437Tree_19680.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19680 [] [] 0 odd437Tree_9838 odd437Tree_19679
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_9838 odd437_valid_19679

theorem odd437_sorted_19680 : odd437Tree_19680.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19680 [] [] 0 odd437Tree_9838 odd437Tree_19679
    rfl (by decide +kernel) odd437_sorted_9838 odd437_sorted_19679

theorem odd437_queries_19680 : odd437Tree_19680.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19680 [] [] 0 odd437Tree_9838 odd437Tree_19679
    rfl odd437_queries_9838 odd437_queries_19679

-- 76 source leaves.
theorem odd437_valid_19831 : odd437Tree_19831.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19831 : odd437Tree_19831.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19831 : odd437Tree_19831.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_19984 : odd437Tree_19984.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_19984 : odd437Tree_19984.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_19984 : odd437Tree_19984.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_19985 : odd437Tree_19985.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_19985 [11] [16] 10817693892445 odd437Tree_19831 odd437Tree_19984
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19831 odd437_valid_19984

theorem odd437_sorted_19985 : odd437Tree_19985.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_19985 [11] [16] 10817693892445 odd437Tree_19831 odd437Tree_19984
    rfl (by decide +kernel) odd437_sorted_19831 odd437_sorted_19984

theorem odd437_queries_19985 : odd437Tree_19985.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_19985 [11] [16] 10817693892445 odd437Tree_19831 odd437Tree_19984
    rfl odd437_queries_19831 odd437_queries_19984

-- 77 source leaves.
theorem odd437_valid_20138 : odd437Tree_20138.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20138 : odd437Tree_20138.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20138 : odd437Tree_20138.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_20291 : odd437Tree_20291.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20291 : odd437Tree_20291.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20291 : odd437Tree_20291.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_20292 : odd437Tree_20292.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20292 [11] [16] 19664503279476 odd437Tree_20138 odd437Tree_20291
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20138 odd437_valid_20291

theorem odd437_sorted_20292 : odd437Tree_20292.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20292 [11] [16] 19664503279476 odd437Tree_20138 odd437Tree_20291
    rfl (by decide +kernel) odd437_sorted_20138 odd437_sorted_20291

theorem odd437_queries_20292 : odd437Tree_20292.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20292 [11] [16] 19664503279476 odd437Tree_20138 odd437Tree_20291
    rfl odd437_queries_20138 odd437_queries_20291

-- 307 source leaves.
theorem odd437_valid_20293 : odd437Tree_20293.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20293 [11] [16] 10817693892445 odd437Tree_19985 odd437Tree_20292
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19985 odd437_valid_20292

theorem odd437_sorted_20293 : odd437Tree_20293.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20293 [11] [16] 10817693892445 odd437Tree_19985 odd437Tree_20292
    rfl (by decide +kernel) odd437_sorted_19985 odd437_sorted_20292

theorem odd437_queries_20293 : odd437Tree_20293.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20293 [11] [16] 10817693892445 odd437Tree_19985 odd437Tree_20292
    rfl odd437_queries_19985 odd437_queries_20292

-- 77 source leaves.
theorem odd437_valid_20446 : odd437Tree_20446.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20446 : odd437Tree_20446.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20446 : odd437Tree_20446.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_20599 : odd437Tree_20599.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20599 : odd437Tree_20599.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20599 : odd437Tree_20599.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_20600 : odd437Tree_20600.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20600 [11] [] 22080559692421 odd437Tree_20446 odd437Tree_20599
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20446 odd437_valid_20599

theorem odd437_sorted_20600 : odd437Tree_20600.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20600 [11] [] 22080559692421 odd437Tree_20446 odd437Tree_20599
    rfl (by decide +kernel) odd437_sorted_20446 odd437_sorted_20599

theorem odd437_queries_20600 : odd437Tree_20600.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20600 [11] [] 22080559692421 odd437Tree_20446 odd437Tree_20599
    rfl odd437_queries_20446 odd437_queries_20599

-- 77 source leaves.
theorem odd437_valid_20753 : odd437Tree_20753.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20753 : odd437Tree_20753.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20753 : odd437Tree_20753.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_20906 : odd437Tree_20906.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_20906 : odd437Tree_20906.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_20906 : odd437Tree_20906.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_20907 : odd437Tree_20907.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20907 [11] [19] 26040694627107 odd437Tree_20753 odd437Tree_20906
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20753 odd437_valid_20906

theorem odd437_sorted_20907 : odd437Tree_20907.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20907 [11] [19] 26040694627107 odd437Tree_20753 odd437Tree_20906
    rfl (by decide +kernel) odd437_sorted_20753 odd437_sorted_20906

theorem odd437_queries_20907 : odd437Tree_20907.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20907 [11] [19] 26040694627107 odd437Tree_20753 odd437Tree_20906
    rfl odd437_queries_20753 odd437_queries_20906

-- 308 source leaves.
theorem odd437_valid_20908 : odd437Tree_20908.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20908 [11] [] 22080559692421 odd437Tree_20600 odd437Tree_20907
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20600 odd437_valid_20907

theorem odd437_sorted_20908 : odd437Tree_20908.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20908 [11] [] 22080559692421 odd437Tree_20600 odd437Tree_20907
    rfl (by decide +kernel) odd437_sorted_20600 odd437_sorted_20907

theorem odd437_queries_20908 : odd437Tree_20908.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20908 [11] [] 22080559692421 odd437Tree_20600 odd437Tree_20907
    rfl odd437_queries_20600 odd437_queries_20907

-- 615 source leaves.
theorem odd437_valid_20909 : odd437Tree_20909.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_20909 [11] [] 10817693892445 odd437Tree_20293 odd437Tree_20908
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20293 odd437_valid_20908

theorem odd437_sorted_20909 : odd437Tree_20909.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_20909 [11] [] 10817693892445 odd437Tree_20293 odd437Tree_20908
    rfl (by decide +kernel) odd437_sorted_20293 odd437_sorted_20908

theorem odd437_queries_20909 : odd437Tree_20909.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_20909 [11] [] 10817693892445 odd437Tree_20293 odd437Tree_20908
    rfl odd437_queries_20293 odd437_queries_20908

-- 76 source leaves.
theorem odd437_valid_21060 : odd437Tree_21060.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21060 : odd437Tree_21060.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21060 : odd437Tree_21060.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_21213 : odd437Tree_21213.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21213 : odd437Tree_21213.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21213 : odd437Tree_21213.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_21214 : odd437Tree_21214.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_21214 [11] [19] 27319507173395 odd437Tree_21060 odd437Tree_21213
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21060 odd437_valid_21213

theorem odd437_sorted_21214 : odd437Tree_21214.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_21214 [11] [19] 27319507173395 odd437Tree_21060 odd437Tree_21213
    rfl (by decide +kernel) odd437_sorted_21060 odd437_sorted_21213

theorem odd437_queries_21214 : odd437Tree_21214.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_21214 [11] [19] 27319507173395 odd437Tree_21060 odd437Tree_21213
    rfl odd437_queries_21060 odd437_queries_21213

-- 77 source leaves.
theorem odd437_valid_21367 : odd437Tree_21367.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21367 : odd437Tree_21367.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21367 : odd437Tree_21367.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_21520 : odd437Tree_21520.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21520 : odd437Tree_21520.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21520 : odd437Tree_21520.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_21521 : odd437Tree_21521.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_21521 [11] [19] 27542772215417 odd437Tree_21367 odd437Tree_21520
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21367 odd437_valid_21520

theorem odd437_sorted_21521 : odd437Tree_21521.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_21521 [11] [19] 27542772215417 odd437Tree_21367 odd437Tree_21520
    rfl (by decide +kernel) odd437_sorted_21367 odd437_sorted_21520

theorem odd437_queries_21521 : odd437Tree_21521.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_21521 [11] [19] 27542772215417 odd437Tree_21367 odd437Tree_21520
    rfl odd437_queries_21367 odd437_queries_21520

-- 307 source leaves.
theorem odd437_valid_21522 : odd437Tree_21522.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_21522 [11] [19] 27319507173395 odd437Tree_21214 odd437Tree_21521
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21214 odd437_valid_21521

theorem odd437_sorted_21522 : odd437Tree_21522.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_21522 [11] [19] 27319507173395 odd437Tree_21214 odd437Tree_21521
    rfl (by decide +kernel) odd437_sorted_21214 odd437_sorted_21521

theorem odd437_queries_21522 : odd437Tree_21522.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_21522 [11] [19] 27319507173395 odd437Tree_21214 odd437Tree_21521
    rfl odd437_queries_21214 odd437_queries_21521

-- 77 source leaves.
theorem odd437_valid_21675 : odd437Tree_21675.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21675 : odd437Tree_21675.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21675 : odd437Tree_21675.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_21828 : odd437Tree_21828.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21828 : odd437Tree_21828.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21828 : odd437Tree_21828.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_21829 : odd437Tree_21829.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_21829 [11] [19] 31906147011674 odd437Tree_21675 odd437Tree_21828
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21675 odd437_valid_21828

theorem odd437_sorted_21829 : odd437Tree_21829.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_21829 [11] [19] 31906147011674 odd437Tree_21675 odd437Tree_21828
    rfl (by decide +kernel) odd437_sorted_21675 odd437_sorted_21828

theorem odd437_queries_21829 : odd437Tree_21829.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_21829 [11] [19] 31906147011674 odd437Tree_21675 odd437Tree_21828
    rfl odd437_queries_21675 odd437_queries_21828

-- 77 source leaves.
theorem odd437_valid_21982 : odd437Tree_21982.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_21982 : odd437Tree_21982.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_21982 : odd437Tree_21982.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_22135 : odd437Tree_22135.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22135 : odd437Tree_22135.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22135 : odd437Tree_22135.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_22136 : odd437Tree_22136.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22136 [11] [] 33539662637840 odd437Tree_21982 odd437Tree_22135
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21982 odd437_valid_22135

theorem odd437_sorted_22136 : odd437Tree_22136.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22136 [11] [] 33539662637840 odd437Tree_21982 odd437Tree_22135
    rfl (by decide +kernel) odd437_sorted_21982 odd437_sorted_22135

theorem odd437_queries_22136 : odd437Tree_22136.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22136 [11] [] 33539662637840 odd437Tree_21982 odd437Tree_22135
    rfl odd437_queries_21982 odd437_queries_22135

-- 308 source leaves.
theorem odd437_valid_22137 : odd437Tree_22137.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22137 [11] [] 31906147011674 odd437Tree_21829 odd437Tree_22136
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21829 odd437_valid_22136

theorem odd437_sorted_22137 : odd437Tree_22137.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22137 [11] [] 31906147011674 odd437Tree_21829 odd437Tree_22136
    rfl (by decide +kernel) odd437_sorted_21829 odd437_sorted_22136

theorem odd437_queries_22137 : odd437Tree_22137.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22137 [11] [] 31906147011674 odd437Tree_21829 odd437Tree_22136
    rfl odd437_queries_21829 odd437_queries_22136

-- 615 source leaves.
theorem odd437_valid_22138 : odd437Tree_22138.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22138 [11] [] 27319507173395 odd437Tree_21522 odd437Tree_22137
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_21522 odd437_valid_22137

theorem odd437_sorted_22138 : odd437Tree_22138.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22138 [11] [] 27319507173395 odd437Tree_21522 odd437Tree_22137
    rfl (by decide +kernel) odd437_sorted_21522 odd437_sorted_22137

theorem odd437_queries_22138 : odd437Tree_22138.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22138 [11] [] 27319507173395 odd437Tree_21522 odd437Tree_22137
    rfl odd437_queries_21522 odd437_queries_22137

-- 1230 source leaves.
theorem odd437_valid_22139 : odd437Tree_22139.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22139 [11] [] 10817693892445 odd437Tree_20909 odd437Tree_22138
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_20909 odd437_valid_22138

theorem odd437_sorted_22139 : odd437Tree_22139.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22139 [11] [] 10817693892445 odd437Tree_20909 odd437Tree_22138
    rfl (by decide +kernel) odd437_sorted_20909 odd437_sorted_22138

theorem odd437_queries_22139 : odd437Tree_22139.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22139 [11] [] 10817693892445 odd437Tree_20909 odd437Tree_22138
    rfl odd437_queries_20909 odd437_queries_22138

-- 76 source leaves.
theorem odd437_valid_22290 : odd437Tree_22290.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22290 : odd437Tree_22290.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22290 : odd437Tree_22290.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_22443 : odd437Tree_22443.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22443 : odd437Tree_22443.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22443 : odd437Tree_22443.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_22444 : odd437Tree_22444.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22444 [11] [20] 37358528419384 odd437Tree_22290 odd437Tree_22443
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22290 odd437_valid_22443

theorem odd437_sorted_22444 : odd437Tree_22444.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22444 [11] [20] 37358528419384 odd437Tree_22290 odd437Tree_22443
    rfl (by decide +kernel) odd437_sorted_22290 odd437_sorted_22443

theorem odd437_queries_22444 : odd437Tree_22444.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22444 [11] [20] 37358528419384 odd437Tree_22290 odd437Tree_22443
    rfl odd437_queries_22290 odd437_queries_22443

-- 77 source leaves.
theorem odd437_valid_22597 : odd437Tree_22597.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22597 : odd437Tree_22597.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22597 : odd437Tree_22597.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_22750 : odd437Tree_22750.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22750 : odd437Tree_22750.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22750 : odd437Tree_22750.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_22751 : odd437Tree_22751.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22751 [11] [20] 36246242492319 odd437Tree_22597 odd437Tree_22750
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22597 odd437_valid_22750

theorem odd437_sorted_22751 : odd437Tree_22751.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22751 [11] [20] 36246242492319 odd437Tree_22597 odd437Tree_22750
    rfl (by decide +kernel) odd437_sorted_22597 odd437_sorted_22750

theorem odd437_queries_22751 : odd437Tree_22751.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22751 [11] [20] 36246242492319 odd437Tree_22597 odd437Tree_22750
    rfl odd437_queries_22597 odd437_queries_22750

-- 307 source leaves.
theorem odd437_valid_22752 : odd437Tree_22752.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_22752 [11] [20] 36246242492319 odd437Tree_22444 odd437Tree_22751
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22444 odd437_valid_22751

theorem odd437_sorted_22752 : odd437Tree_22752.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_22752 [11] [20] 36246242492319 odd437Tree_22444 odd437Tree_22751
    rfl (by decide +kernel) odd437_sorted_22444 odd437_sorted_22751

theorem odd437_queries_22752 : odd437Tree_22752.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_22752 [11] [20] 36246242492319 odd437Tree_22444 odd437Tree_22751
    rfl odd437_queries_22444 odd437_queries_22751

-- 77 source leaves.
theorem odd437_valid_22905 : odd437Tree_22905.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_22905 : odd437Tree_22905.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_22905 : odd437Tree_22905.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_23058 : odd437Tree_23058.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23058 : odd437Tree_23058.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23058 : odd437Tree_23058.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_23059 : odd437Tree_23059.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23059 [11] [20] 37134155534996 odd437Tree_22905 odd437Tree_23058
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22905 odd437_valid_23058

theorem odd437_sorted_23059 : odd437Tree_23059.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23059 [11] [20] 37134155534996 odd437Tree_22905 odd437Tree_23058
    rfl (by decide +kernel) odd437_sorted_22905 odd437_sorted_23058

theorem odd437_queries_23059 : odd437Tree_23059.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23059 [11] [20] 37134155534996 odd437Tree_22905 odd437Tree_23058
    rfl odd437_queries_22905 odd437_queries_23058

-- 77 source leaves.
theorem odd437_valid_23212 : odd437Tree_23212.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23212 : odd437Tree_23212.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23212 : odd437Tree_23212.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_23365 : odd437Tree_23365.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23365 : odd437Tree_23365.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23365 : odd437Tree_23365.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_23366 : odd437Tree_23366.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23366 [] [] 6629479817058 odd437Tree_23212 odd437Tree_23365
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23212 odd437_valid_23365

theorem odd437_sorted_23366 : odd437Tree_23366.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23366 [] [] 6629479817058 odd437Tree_23212 odd437Tree_23365
    rfl (by decide +kernel) odd437_sorted_23212 odd437_sorted_23365

theorem odd437_queries_23366 : odd437Tree_23366.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23366 [] [] 6629479817058 odd437Tree_23212 odd437Tree_23365
    rfl odd437_queries_23212 odd437_queries_23365

-- 308 source leaves.
theorem odd437_valid_23367 : odd437Tree_23367.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23367 [] [] 6629479817058 odd437Tree_23059 odd437Tree_23366
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23059 odd437_valid_23366

theorem odd437_sorted_23367 : odd437Tree_23367.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23367 [] [] 6629479817058 odd437Tree_23059 odd437Tree_23366
    rfl (by decide +kernel) odd437_sorted_23059 odd437_sorted_23366

theorem odd437_queries_23367 : odd437Tree_23367.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23367 [] [] 6629479817058 odd437Tree_23059 odd437Tree_23366
    rfl odd437_queries_23059 odd437_queries_23366

-- 615 source leaves.
theorem odd437_valid_23368 : odd437Tree_23368.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23368 [] [] 6629479817058 odd437Tree_22752 odd437Tree_23367
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22752 odd437_valid_23367

theorem odd437_sorted_23368 : odd437Tree_23368.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23368 [] [] 6629479817058 odd437Tree_22752 odd437Tree_23367
    rfl (by decide +kernel) odd437_sorted_22752 odd437_sorted_23367

theorem odd437_queries_23368 : odd437Tree_23368.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23368 [] [] 6629479817058 odd437Tree_22752 odd437Tree_23367
    rfl odd437_queries_22752 odd437_queries_23367

-- 76 source leaves.
theorem odd437_valid_23519 : odd437Tree_23519.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23519 : odd437Tree_23519.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23519 : odd437Tree_23519.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_23672 : odd437Tree_23672.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23672 : odd437Tree_23672.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23672 : odd437Tree_23672.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_23673 : odd437Tree_23673.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23673 [14] [6] 5230801035456 odd437Tree_23519 odd437Tree_23672
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23519 odd437_valid_23672

theorem odd437_sorted_23673 : odd437Tree_23673.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23673 [14] [6] 5230801035456 odd437Tree_23519 odd437Tree_23672
    rfl (by decide +kernel) odd437_sorted_23519 odd437_sorted_23672

theorem odd437_queries_23673 : odd437Tree_23673.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23673 [14] [6] 5230801035456 odd437Tree_23519 odd437Tree_23672
    rfl odd437_queries_23519 odd437_queries_23672

-- 77 source leaves.
theorem odd437_valid_23826 : odd437Tree_23826.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23826 : odd437Tree_23826.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23826 : odd437Tree_23826.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_23979 : odd437Tree_23979.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_23979 : odd437Tree_23979.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_23979 : odd437Tree_23979.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_23980 : odd437Tree_23980.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23980 [14] [6] 4001691700794 odd437Tree_23826 odd437Tree_23979
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23826 odd437_valid_23979

theorem odd437_sorted_23980 : odd437Tree_23980.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23980 [14] [6] 4001691700794 odd437Tree_23826 odd437Tree_23979
    rfl (by decide +kernel) odd437_sorted_23826 odd437_sorted_23979

theorem odd437_queries_23980 : odd437Tree_23980.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23980 [14] [6] 4001691700794 odd437Tree_23826 odd437Tree_23979
    rfl odd437_queries_23826 odd437_queries_23979

-- 307 source leaves.
theorem odd437_valid_23981 : odd437Tree_23981.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_23981 [14] [6] 4001691700794 odd437Tree_23673 odd437Tree_23980
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23673 odd437_valid_23980

theorem odd437_sorted_23981 : odd437Tree_23981.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_23981 [14] [6] 4001691700794 odd437Tree_23673 odd437Tree_23980
    rfl (by decide +kernel) odd437_sorted_23673 odd437_sorted_23980

theorem odd437_queries_23981 : odd437Tree_23981.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_23981 [14] [6] 4001691700794 odd437Tree_23673 odd437Tree_23980
    rfl odd437_queries_23673 odd437_queries_23980

-- 77 source leaves.
theorem odd437_valid_24134 : odd437Tree_24134.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24134 : odd437Tree_24134.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24134 : odd437Tree_24134.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_24287 : odd437Tree_24287.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24287 : odd437Tree_24287.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24287 : odd437Tree_24287.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_24288 : odd437Tree_24288.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24288 [14] [6] 4752518709709 odd437Tree_24134 odd437Tree_24287
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24134 odd437_valid_24287

theorem odd437_sorted_24288 : odd437Tree_24288.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24288 [14] [6] 4752518709709 odd437Tree_24134 odd437Tree_24287
    rfl (by decide +kernel) odd437_sorted_24134 odd437_sorted_24287

theorem odd437_queries_24288 : odd437Tree_24288.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24288 [14] [6] 4752518709709 odd437Tree_24134 odd437Tree_24287
    rfl odd437_queries_24134 odd437_queries_24287

-- 77 source leaves.
theorem odd437_valid_24441 : odd437Tree_24441.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24441 : odd437Tree_24441.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24441 : odd437Tree_24441.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_24594 : odd437Tree_24594.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24594 : odd437Tree_24594.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24594 : odd437Tree_24594.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_24595 : odd437Tree_24595.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24595 [14] [6] 5114017361607 odd437Tree_24441 odd437Tree_24594
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24441 odd437_valid_24594

theorem odd437_sorted_24595 : odd437Tree_24595.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24595 [14] [6] 5114017361607 odd437Tree_24441 odd437Tree_24594
    rfl (by decide +kernel) odd437_sorted_24441 odd437_sorted_24594

theorem odd437_queries_24595 : odd437Tree_24595.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24595 [14] [6] 5114017361607 odd437Tree_24441 odd437Tree_24594
    rfl odd437_queries_24441 odd437_queries_24594

-- 308 source leaves.
theorem odd437_valid_24596 : odd437Tree_24596.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24596 [14] [6] 4752518709709 odd437Tree_24288 odd437Tree_24595
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24288 odd437_valid_24595

theorem odd437_sorted_24596 : odd437Tree_24596.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24596 [14] [6] 4752518709709 odd437Tree_24288 odd437Tree_24595
    rfl (by decide +kernel) odd437_sorted_24288 odd437_sorted_24595

theorem odd437_queries_24596 : odd437Tree_24596.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24596 [14] [6] 4752518709709 odd437Tree_24288 odd437Tree_24595
    rfl odd437_queries_24288 odd437_queries_24595

-- 615 source leaves.
theorem odd437_valid_24597 : odd437Tree_24597.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24597 [14] [6] 4001691700794 odd437Tree_23981 odd437Tree_24596
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23981 odd437_valid_24596

theorem odd437_sorted_24597 : odd437Tree_24597.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24597 [14] [6] 4001691700794 odd437Tree_23981 odd437Tree_24596
    rfl (by decide +kernel) odd437_sorted_23981 odd437_sorted_24596

theorem odd437_queries_24597 : odd437Tree_24597.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24597 [14] [6] 4001691700794 odd437Tree_23981 odd437Tree_24596
    rfl odd437_queries_23981 odd437_queries_24596

-- 1230 source leaves.
theorem odd437_valid_24598 : odd437Tree_24598.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24598 [] [] 4001691700794 odd437Tree_23368 odd437Tree_24597
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_23368 odd437_valid_24597

theorem odd437_sorted_24598 : odd437Tree_24598.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24598 [] [] 4001691700794 odd437Tree_23368 odd437Tree_24597
    rfl (by decide +kernel) odd437_sorted_23368 odd437_sorted_24597

theorem odd437_queries_24598 : odd437Tree_24598.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24598 [] [] 4001691700794 odd437Tree_23368 odd437Tree_24597
    rfl odd437_queries_23368 odd437_queries_24597

-- 2460 source leaves.
theorem odd437_valid_24599 : odd437Tree_24599.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24599 [] [] 4001691700794 odd437Tree_22139 odd437Tree_24598
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_22139 odd437_valid_24598

theorem odd437_sorted_24599 : odd437Tree_24599.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24599 [] [] 4001691700794 odd437Tree_22139 odd437Tree_24598
    rfl (by decide +kernel) odd437_sorted_22139 odd437_sorted_24598

theorem odd437_queries_24599 : odd437Tree_24599.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24599 [] [] 4001691700794 odd437Tree_22139 odd437Tree_24598
    rfl odd437_queries_22139 odd437_queries_24598

-- 76 source leaves.
theorem odd437_valid_24750 : odd437Tree_24750.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24750 : odd437Tree_24750.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24750 : odd437Tree_24750.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_24903 : odd437Tree_24903.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_24903 : odd437Tree_24903.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_24903 : odd437Tree_24903.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_24904 : odd437Tree_24904.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_24904 [14] [] 8590013520572 odd437Tree_24750 odd437Tree_24903
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24750 odd437_valid_24903

theorem odd437_sorted_24904 : odd437Tree_24904.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_24904 [14] [] 8590013520572 odd437Tree_24750 odd437Tree_24903
    rfl (by decide +kernel) odd437_sorted_24750 odd437_sorted_24903

theorem odd437_queries_24904 : odd437Tree_24904.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_24904 [14] [] 8590013520572 odd437Tree_24750 odd437Tree_24903
    rfl odd437_queries_24750 odd437_queries_24903

-- 77 source leaves.
theorem odd437_valid_25057 : odd437Tree_25057.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25057 : odd437Tree_25057.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25057 : odd437Tree_25057.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_25210 : odd437Tree_25210.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25210 : odd437Tree_25210.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25210 : odd437Tree_25210.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_25211 : odd437Tree_25211.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25211 [14] [9] 63005542927913 odd437Tree_25057 odd437Tree_25210
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25057 odd437_valid_25210

theorem odd437_sorted_25211 : odd437Tree_25211.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25211 [14] [9] 63005542927913 odd437Tree_25057 odd437Tree_25210
    rfl (by decide +kernel) odd437_sorted_25057 odd437_sorted_25210

theorem odd437_queries_25211 : odd437Tree_25211.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25211 [14] [9] 63005542927913 odd437Tree_25057 odd437Tree_25210
    rfl odd437_queries_25057 odd437_queries_25210

-- 307 source leaves.
theorem odd437_valid_25212 : odd437Tree_25212.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25212 [14] [] 8590013520572 odd437Tree_24904 odd437Tree_25211
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24904 odd437_valid_25211

theorem odd437_sorted_25212 : odd437Tree_25212.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25212 [14] [] 8590013520572 odd437Tree_24904 odd437Tree_25211
    rfl (by decide +kernel) odd437_sorted_24904 odd437_sorted_25211

theorem odd437_queries_25212 : odd437Tree_25212.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25212 [14] [] 8590013520572 odd437Tree_24904 odd437Tree_25211
    rfl odd437_queries_24904 odd437_queries_25211

-- 77 source leaves.
theorem odd437_valid_25365 : odd437Tree_25365.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25365 : odd437Tree_25365.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25365 : odd437Tree_25365.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_25518 : odd437Tree_25518.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25518 : odd437Tree_25518.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25518 : odd437Tree_25518.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_25519 : odd437Tree_25519.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25519 [14] [9] 63375339444717 odd437Tree_25365 odd437Tree_25518
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25365 odd437_valid_25518

theorem odd437_sorted_25519 : odd437Tree_25519.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25519 [14] [9] 63375339444717 odd437Tree_25365 odd437Tree_25518
    rfl (by decide +kernel) odd437_sorted_25365 odd437_sorted_25518

theorem odd437_queries_25519 : odd437Tree_25519.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25519 [14] [9] 63375339444717 odd437Tree_25365 odd437Tree_25518
    rfl odd437_queries_25365 odd437_queries_25518

-- 77 source leaves.
theorem odd437_valid_25672 : odd437Tree_25672.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25672 : odd437Tree_25672.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25672 : odd437Tree_25672.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_25825 : odd437Tree_25825.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25825 : odd437Tree_25825.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25825 : odd437Tree_25825.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_25826 : odd437Tree_25826.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25826 [14] [9] 64888261077309 odd437Tree_25672 odd437Tree_25825
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25672 odd437_valid_25825

theorem odd437_sorted_25826 : odd437Tree_25826.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25826 [14] [9] 64888261077309 odd437Tree_25672 odd437Tree_25825
    rfl (by decide +kernel) odd437_sorted_25672 odd437_sorted_25825

theorem odd437_queries_25826 : odd437Tree_25826.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25826 [14] [9] 64888261077309 odd437Tree_25672 odd437Tree_25825
    rfl odd437_queries_25672 odd437_queries_25825

-- 308 source leaves.
theorem odd437_valid_25827 : odd437Tree_25827.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25827 [14] [9] 63375339444717 odd437Tree_25519 odd437Tree_25826
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25519 odd437_valid_25826

theorem odd437_sorted_25827 : odd437Tree_25827.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25827 [14] [9] 63375339444717 odd437Tree_25519 odd437Tree_25826
    rfl (by decide +kernel) odd437_sorted_25519 odd437_sorted_25826

theorem odd437_queries_25827 : odd437Tree_25827.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25827 [14] [9] 63375339444717 odd437Tree_25519 odd437Tree_25826
    rfl odd437_queries_25519 odd437_queries_25826

-- 615 source leaves.
theorem odd437_valid_25828 : odd437Tree_25828.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_25828 [14] [] 8590013520572 odd437Tree_25212 odd437Tree_25827
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25212 odd437_valid_25827

theorem odd437_sorted_25828 : odd437Tree_25828.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_25828 [14] [] 8590013520572 odd437Tree_25212 odd437Tree_25827
    rfl (by decide +kernel) odd437_sorted_25212 odd437_sorted_25827

theorem odd437_queries_25828 : odd437Tree_25828.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_25828 [14] [] 8590013520572 odd437Tree_25212 odd437Tree_25827
    rfl odd437_queries_25212 odd437_queries_25827

-- 76 source leaves.
theorem odd437_valid_25979 : odd437Tree_25979.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_25979 : odd437Tree_25979.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_25979 : odd437Tree_25979.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_26132 : odd437Tree_26132.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26132 : odd437Tree_26132.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26132 : odd437Tree_26132.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_26133 : odd437Tree_26133.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_26133 [14] [9] 63005542927913 odd437Tree_25979 odd437Tree_26132
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25979 odd437_valid_26132

theorem odd437_sorted_26133 : odd437Tree_26133.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_26133 [14] [9] 63005542927913 odd437Tree_25979 odd437Tree_26132
    rfl (by decide +kernel) odd437_sorted_25979 odd437_sorted_26132

theorem odd437_queries_26133 : odd437Tree_26133.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_26133 [14] [9] 63005542927913 odd437Tree_25979 odd437Tree_26132
    rfl odd437_queries_25979 odd437_queries_26132

-- 77 source leaves.
theorem odd437_valid_26286 : odd437Tree_26286.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26286 : odd437Tree_26286.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26286 : odd437Tree_26286.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_26439 : odd437Tree_26439.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26439 : odd437Tree_26439.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26439 : odd437Tree_26439.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_26440 : odd437Tree_26440.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_26440 [14] [] 63971180772995 odd437Tree_26286 odd437Tree_26439
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26286 odd437_valid_26439

theorem odd437_sorted_26440 : odd437Tree_26440.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_26440 [14] [] 63971180772995 odd437Tree_26286 odd437Tree_26439
    rfl (by decide +kernel) odd437_sorted_26286 odd437_sorted_26439

theorem odd437_queries_26440 : odd437Tree_26440.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_26440 [14] [] 63971180772995 odd437Tree_26286 odd437Tree_26439
    rfl odd437_queries_26286 odd437_queries_26439

-- 307 source leaves.
theorem odd437_valid_26441 : odd437Tree_26441.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_26441 [14] [] 63005542927913 odd437Tree_26133 odd437Tree_26440
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26133 odd437_valid_26440

theorem odd437_sorted_26441 : odd437Tree_26441.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_26441 [14] [] 63005542927913 odd437Tree_26133 odd437Tree_26440
    rfl (by decide +kernel) odd437_sorted_26133 odd437_sorted_26440

theorem odd437_queries_26441 : odd437Tree_26441.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_26441 [14] [] 63005542927913 odd437Tree_26133 odd437Tree_26440
    rfl odd437_queries_26133 odd437_queries_26440

-- 77 source leaves.
theorem odd437_valid_26594 : odd437Tree_26594.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26594 : odd437Tree_26594.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26594 : odd437Tree_26594.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_26747 : odd437Tree_26747.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26747 : odd437Tree_26747.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26747 : odd437Tree_26747.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_26748 : odd437Tree_26748.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_26748 [14] [22] 72411983138185 odd437Tree_26594 odd437Tree_26747
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26594 odd437_valid_26747

theorem odd437_sorted_26748 : odd437Tree_26748.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_26748 [14] [22] 72411983138185 odd437Tree_26594 odd437Tree_26747
    rfl (by decide +kernel) odd437_sorted_26594 odd437_sorted_26747

theorem odd437_queries_26748 : odd437Tree_26748.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_26748 [14] [22] 72411983138185 odd437Tree_26594 odd437Tree_26747
    rfl odd437_queries_26594 odd437_queries_26747

-- 77 source leaves.
theorem odd437_valid_26901 : odd437Tree_26901.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_26901 : odd437Tree_26901.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_26901 : odd437Tree_26901.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_27054 : odd437Tree_27054.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27054 : odd437Tree_27054.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27054 : odd437Tree_27054.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_27055 : odd437Tree_27055.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27055 [14] [22] 76838433310655 odd437Tree_26901 odd437Tree_27054
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26901 odd437_valid_27054

theorem odd437_sorted_27055 : odd437Tree_27055.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27055 [14] [22] 76838433310655 odd437Tree_26901 odd437Tree_27054
    rfl (by decide +kernel) odd437_sorted_26901 odd437_sorted_27054

theorem odd437_queries_27055 : odd437Tree_27055.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27055 [14] [22] 76838433310655 odd437Tree_26901 odd437Tree_27054
    rfl odd437_queries_26901 odd437_queries_27054

-- 308 source leaves.
theorem odd437_valid_27056 : odd437Tree_27056.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27056 [14] [22] 72411983138185 odd437Tree_26748 odd437Tree_27055
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26748 odd437_valid_27055

theorem odd437_sorted_27056 : odd437Tree_27056.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27056 [14] [22] 72411983138185 odd437Tree_26748 odd437Tree_27055
    rfl (by decide +kernel) odd437_sorted_26748 odd437_sorted_27055

theorem odd437_queries_27056 : odd437Tree_27056.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27056 [14] [22] 72411983138185 odd437Tree_26748 odd437Tree_27055
    rfl odd437_queries_26748 odd437_queries_27055

-- 615 source leaves.
theorem odd437_valid_27057 : odd437Tree_27057.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27057 [14] [] 63005542927913 odd437Tree_26441 odd437Tree_27056
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_26441 odd437_valid_27056

theorem odd437_sorted_27057 : odd437Tree_27057.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27057 [14] [] 63005542927913 odd437Tree_26441 odd437Tree_27056
    rfl (by decide +kernel) odd437_sorted_26441 odd437_sorted_27056

theorem odd437_queries_27057 : odd437Tree_27057.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27057 [14] [] 63005542927913 odd437Tree_26441 odd437Tree_27056
    rfl odd437_queries_26441 odd437_queries_27056

-- 1230 source leaves.
theorem odd437_valid_27058 : odd437Tree_27058.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27058 [14] [] 8590013520572 odd437Tree_25828 odd437Tree_27057
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_25828 odd437_valid_27057

theorem odd437_sorted_27058 : odd437Tree_27058.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27058 [14] [] 8590013520572 odd437Tree_25828 odd437Tree_27057
    rfl (by decide +kernel) odd437_sorted_25828 odd437_sorted_27057

theorem odd437_queries_27058 : odd437Tree_27058.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27058 [14] [] 8590013520572 odd437Tree_25828 odd437Tree_27057
    rfl odd437_queries_25828 odd437_queries_27057

-- 76 source leaves.
theorem odd437_valid_27209 : odd437Tree_27209.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27209 : odd437Tree_27209.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27209 : odd437Tree_27209.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_27362 : odd437Tree_27362.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27362 : odd437Tree_27362.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27362 : odd437Tree_27362.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_27363 : odd437Tree_27363.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27363 [14] [22] 73110032274945 odd437Tree_27209 odd437Tree_27362
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27209 odd437_valid_27362

theorem odd437_sorted_27363 : odd437Tree_27363.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27363 [14] [22] 73110032274945 odd437Tree_27209 odd437Tree_27362
    rfl (by decide +kernel) odd437_sorted_27209 odd437_sorted_27362

theorem odd437_queries_27363 : odd437Tree_27363.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27363 [14] [22] 73110032274945 odd437Tree_27209 odd437Tree_27362
    rfl odd437_queries_27209 odd437_queries_27362

-- 77 source leaves.
theorem odd437_valid_27516 : odd437Tree_27516.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27516 : odd437Tree_27516.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27516 : odd437Tree_27516.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_27669 : odd437Tree_27669.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27669 : odd437Tree_27669.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27669 : odd437Tree_27669.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_27670 : odd437Tree_27670.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27670 [14] [22] 73503877138869 odd437Tree_27516 odd437Tree_27669
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27516 odd437_valid_27669

theorem odd437_sorted_27670 : odd437Tree_27670.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27670 [14] [22] 73503877138869 odd437Tree_27516 odd437Tree_27669
    rfl (by decide +kernel) odd437_sorted_27516 odd437_sorted_27669

theorem odd437_queries_27670 : odd437Tree_27670.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27670 [14] [22] 73503877138869 odd437Tree_27516 odd437Tree_27669
    rfl odd437_queries_27516 odd437_queries_27669

-- 307 source leaves.
theorem odd437_valid_27671 : odd437Tree_27671.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27671 [14] [22] 73110032274945 odd437Tree_27363 odd437Tree_27670
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27363 odd437_valid_27670

theorem odd437_sorted_27671 : odd437Tree_27671.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27671 [14] [22] 73110032274945 odd437Tree_27363 odd437Tree_27670
    rfl (by decide +kernel) odd437_sorted_27363 odd437_sorted_27670

theorem odd437_queries_27671 : odd437Tree_27671.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27671 [14] [22] 73110032274945 odd437Tree_27363 odd437Tree_27670
    rfl odd437_queries_27363 odd437_queries_27670

-- 77 source leaves.
theorem odd437_valid_27824 : odd437Tree_27824.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27824 : odd437Tree_27824.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27824 : odd437Tree_27824.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_27977 : odd437Tree_27977.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_27977 : odd437Tree_27977.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_27977 : odd437Tree_27977.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_27978 : odd437Tree_27978.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_27978 [] [] 41668990945690 odd437Tree_27824 odd437Tree_27977
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27824 odd437_valid_27977

theorem odd437_sorted_27978 : odd437Tree_27978.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_27978 [] [] 41668990945690 odd437Tree_27824 odd437Tree_27977
    rfl (by decide +kernel) odd437_sorted_27824 odd437_sorted_27977

theorem odd437_queries_27978 : odd437Tree_27978.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_27978 [] [] 41668990945690 odd437Tree_27824 odd437Tree_27977
    rfl odd437_queries_27824 odd437_queries_27977

-- 77 source leaves.
theorem odd437_valid_28131 : odd437Tree_28131.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28131 : odd437Tree_28131.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28131 : odd437Tree_28131.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_28284 : odd437Tree_28284.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28284 : odd437Tree_28284.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28284 : odd437Tree_28284.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_28285 : odd437Tree_28285.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28285 [16] [10] 41668990945690 odd437Tree_28131 odd437Tree_28284
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28131 odd437_valid_28284

theorem odd437_sorted_28285 : odd437Tree_28285.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28285 [16] [10] 41668990945690 odd437Tree_28131 odd437Tree_28284
    rfl (by decide +kernel) odd437_sorted_28131 odd437_sorted_28284

theorem odd437_queries_28285 : odd437Tree_28285.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28285 [16] [10] 41668990945690 odd437Tree_28131 odd437Tree_28284
    rfl odd437_queries_28131 odd437_queries_28284

-- 308 source leaves.
theorem odd437_valid_28286 : odd437Tree_28286.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28286 [] [] 41668990945690 odd437Tree_27978 odd437Tree_28285
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27978 odd437_valid_28285

theorem odd437_sorted_28286 : odd437Tree_28286.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28286 [] [] 41668990945690 odd437Tree_27978 odd437Tree_28285
    rfl (by decide +kernel) odd437_sorted_27978 odd437_sorted_28285

theorem odd437_queries_28286 : odd437Tree_28286.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28286 [] [] 41668990945690 odd437Tree_27978 odd437Tree_28285
    rfl odd437_queries_27978 odd437_queries_28285

-- 615 source leaves.
theorem odd437_valid_28287 : odd437Tree_28287.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28287 [] [] 41668990945690 odd437Tree_27671 odd437Tree_28286
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27671 odd437_valid_28286

theorem odd437_sorted_28287 : odd437Tree_28287.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28287 [] [] 41668990945690 odd437Tree_27671 odd437Tree_28286
    rfl (by decide +kernel) odd437_sorted_27671 odd437_sorted_28286

theorem odd437_queries_28287 : odd437Tree_28287.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28287 [] [] 41668990945690 odd437Tree_27671 odd437Tree_28286
    rfl odd437_queries_27671 odd437_queries_28286

-- 77 source leaves.
theorem odd437_valid_28440 : odd437Tree_28440.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28440 : odd437Tree_28440.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28440 : odd437Tree_28440.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_28593 : odd437Tree_28593.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28593 : odd437Tree_28593.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28593 : odd437Tree_28593.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_28594 : odd437Tree_28594.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28594 [16] [10] 41862456748478 odd437Tree_28440 odd437Tree_28593
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28440 odd437_valid_28593

theorem odd437_sorted_28594 : odd437Tree_28594.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28594 [16] [10] 41862456748478 odd437Tree_28440 odd437Tree_28593
    rfl (by decide +kernel) odd437_sorted_28440 odd437_sorted_28593

theorem odd437_queries_28594 : odd437Tree_28594.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28594 [16] [10] 41862456748478 odd437Tree_28440 odd437Tree_28593
    rfl odd437_queries_28440 odd437_queries_28593

-- 77 source leaves.
theorem odd437_valid_28747 : odd437Tree_28747.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28747 : odd437Tree_28747.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28747 : odd437Tree_28747.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_28900 : odd437Tree_28900.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_28900 : odd437Tree_28900.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_28900 : odd437Tree_28900.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_28901 : odd437Tree_28901.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28901 [16] [10] 41937206351655 odd437Tree_28747 odd437Tree_28900
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28747 odd437_valid_28900

theorem odd437_sorted_28901 : odd437Tree_28901.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28901 [16] [10] 41937206351655 odd437Tree_28747 odd437Tree_28900
    rfl (by decide +kernel) odd437_sorted_28747 odd437_sorted_28900

theorem odd437_queries_28901 : odd437Tree_28901.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28901 [16] [10] 41937206351655 odd437Tree_28747 odd437Tree_28900
    rfl odd437_queries_28747 odd437_queries_28900

-- 308 source leaves.
theorem odd437_valid_28902 : odd437Tree_28902.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_28902 [16] [10] 41862456748478 odd437Tree_28594 odd437Tree_28901
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28594 odd437_valid_28901

theorem odd437_sorted_28902 : odd437Tree_28902.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_28902 [16] [10] 41862456748478 odd437Tree_28594 odd437Tree_28901
    rfl (by decide +kernel) odd437_sorted_28594 odd437_sorted_28901

theorem odd437_queries_28902 : odd437Tree_28902.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_28902 [16] [10] 41862456748478 odd437Tree_28594 odd437Tree_28901
    rfl odd437_queries_28594 odd437_queries_28901

-- 77 source leaves.
theorem odd437_valid_29055 : odd437Tree_29055.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29055 : odd437Tree_29055.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29055 : odd437Tree_29055.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_29208 : odd437Tree_29208.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29208 : odd437Tree_29208.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29208 : odd437Tree_29208.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_29209 : odd437Tree_29209.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29209 [16] [] 43638748757535 odd437Tree_29055 odd437Tree_29208
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29055 odd437_valid_29208

theorem odd437_sorted_29209 : odd437Tree_29209.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29209 [16] [] 43638748757535 odd437Tree_29055 odd437Tree_29208
    rfl (by decide +kernel) odd437_sorted_29055 odd437_sorted_29208

theorem odd437_queries_29209 : odd437Tree_29209.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29209 [16] [] 43638748757535 odd437Tree_29055 odd437Tree_29208
    rfl odd437_queries_29055 odd437_queries_29208

-- 77 source leaves.
theorem odd437_valid_29362 : odd437Tree_29362.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29362 : odd437Tree_29362.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29362 : odd437Tree_29362.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_29515 : odd437Tree_29515.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29515 : odd437Tree_29515.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29515 : odd437Tree_29515.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_29516 : odd437Tree_29516.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29516 [16] [12] 63571947923295 odd437Tree_29362 odd437Tree_29515
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29362 odd437_valid_29515

theorem odd437_sorted_29516 : odd437Tree_29516.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29516 [16] [12] 63571947923295 odd437Tree_29362 odd437Tree_29515
    rfl (by decide +kernel) odd437_sorted_29362 odd437_sorted_29515

theorem odd437_queries_29516 : odd437Tree_29516.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29516 [16] [12] 63571947923295 odd437Tree_29362 odd437Tree_29515
    rfl odd437_queries_29362 odd437_queries_29515

-- 308 source leaves.
theorem odd437_valid_29517 : odd437Tree_29517.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29517 [16] [] 43638748757535 odd437Tree_29209 odd437Tree_29516
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29209 odd437_valid_29516

theorem odd437_sorted_29517 : odd437Tree_29517.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29517 [16] [] 43638748757535 odd437Tree_29209 odd437Tree_29516
    rfl (by decide +kernel) odd437_sorted_29209 odd437_sorted_29516

theorem odd437_queries_29517 : odd437Tree_29517.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29517 [16] [] 43638748757535 odd437Tree_29209 odd437Tree_29516
    rfl odd437_queries_29209 odd437_queries_29516

-- 616 source leaves.
theorem odd437_valid_29518 : odd437Tree_29518.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29518 [16] [] 41862456748478 odd437Tree_28902 odd437Tree_29517
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28902 odd437_valid_29517

theorem odd437_sorted_29518 : odd437Tree_29518.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29518 [16] [] 41862456748478 odd437Tree_28902 odd437Tree_29517
    rfl (by decide +kernel) odd437_sorted_28902 odd437_sorted_29517

theorem odd437_queries_29518 : odd437Tree_29518.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29518 [16] [] 41862456748478 odd437Tree_28902 odd437Tree_29517
    rfl odd437_queries_28902 odd437_queries_29517

-- 1231 source leaves.
theorem odd437_valid_29519 : odd437Tree_29519.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29519 [] [] 41668990945690 odd437Tree_28287 odd437Tree_29518
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_28287 odd437_valid_29518

theorem odd437_sorted_29519 : odd437Tree_29519.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29519 [] [] 41668990945690 odd437Tree_28287 odd437Tree_29518
    rfl (by decide +kernel) odd437_sorted_28287 odd437_sorted_29518

theorem odd437_queries_29519 : odd437Tree_29519.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29519 [] [] 41668990945690 odd437Tree_28287 odd437Tree_29518
    rfl odd437_queries_28287 odd437_queries_29518

-- 2461 source leaves.
theorem odd437_valid_29520 : odd437Tree_29520.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29520 [] [] 8590013520572 odd437Tree_27058 odd437Tree_29519
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_27058 odd437_valid_29519

theorem odd437_sorted_29520 : odd437Tree_29520.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29520 [] [] 8590013520572 odd437Tree_27058 odd437Tree_29519
    rfl (by decide +kernel) odd437_sorted_27058 odd437_sorted_29519

theorem odd437_queries_29520 : odd437Tree_29520.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29520 [] [] 8590013520572 odd437Tree_27058 odd437Tree_29519
    rfl odd437_queries_27058 odd437_queries_29519

-- 4921 source leaves.
theorem odd437_valid_29521 : odd437Tree_29521.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29521 [] [] 4001691700794 odd437Tree_24599 odd437Tree_29520
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_24599 odd437_valid_29520

theorem odd437_sorted_29521 : odd437Tree_29521.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29521 [] [] 4001691700794 odd437Tree_24599 odd437Tree_29520
    rfl (by decide +kernel) odd437_sorted_24599 odd437_sorted_29520

theorem odd437_queries_29521 : odd437Tree_29521.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29521 [] [] 4001691700794 odd437Tree_24599 odd437Tree_29520
    rfl odd437_queries_24599 odd437_queries_29520

-- 76 source leaves.
theorem odd437_valid_29672 : odd437Tree_29672.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29672 : odd437Tree_29672.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29672 : odd437Tree_29672.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_29825 : odd437Tree_29825.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29825 : odd437Tree_29825.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29825 : odd437Tree_29825.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_29826 : odd437Tree_29826.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_29826 [16] [12] 62255960816663 odd437Tree_29672 odd437Tree_29825
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29672 odd437_valid_29825

theorem odd437_sorted_29826 : odd437Tree_29826.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_29826 [16] [12] 62255960816663 odd437Tree_29672 odd437Tree_29825
    rfl (by decide +kernel) odd437_sorted_29672 odd437_sorted_29825

theorem odd437_queries_29826 : odd437Tree_29826.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_29826 [16] [12] 62255960816663 odd437Tree_29672 odd437Tree_29825
    rfl odd437_queries_29672 odd437_queries_29825

-- 77 source leaves.
theorem odd437_valid_29979 : odd437Tree_29979.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_29979 : odd437Tree_29979.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_29979 : odd437Tree_29979.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_30132 : odd437Tree_30132.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30132 : odd437Tree_30132.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30132 : odd437Tree_30132.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_30133 : odd437Tree_30133.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30133 [16] [12] 63253084197451 odd437Tree_29979 odd437Tree_30132
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29979 odd437_valid_30132

theorem odd437_sorted_30133 : odd437Tree_30133.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30133 [16] [12] 63253084197451 odd437Tree_29979 odd437Tree_30132
    rfl (by decide +kernel) odd437_sorted_29979 odd437_sorted_30132

theorem odd437_queries_30133 : odd437Tree_30133.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30133 [16] [12] 63253084197451 odd437Tree_29979 odd437Tree_30132
    rfl odd437_queries_29979 odd437_queries_30132

-- 307 source leaves.
theorem odd437_valid_30134 : odd437Tree_30134.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30134 [16] [12] 62255960816663 odd437Tree_29826 odd437Tree_30133
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29826 odd437_valid_30133

theorem odd437_sorted_30134 : odd437Tree_30134.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30134 [16] [12] 62255960816663 odd437Tree_29826 odd437Tree_30133
    rfl (by decide +kernel) odd437_sorted_29826 odd437_sorted_30133

theorem odd437_queries_30134 : odd437Tree_30134.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30134 [16] [12] 62255960816663 odd437Tree_29826 odd437Tree_30133
    rfl odd437_queries_29826 odd437_queries_30133

-- 77 source leaves.
theorem odd437_valid_30287 : odd437Tree_30287.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30287 : odd437Tree_30287.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30287 : odd437Tree_30287.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_30440 : odd437Tree_30440.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30440 : odd437Tree_30440.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30440 : odd437Tree_30440.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_30441 : odd437Tree_30441.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30441 [16] [12] 71197823471821 odd437Tree_30287 odd437Tree_30440
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30287 odd437_valid_30440

theorem odd437_sorted_30441 : odd437Tree_30441.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30441 [16] [12] 71197823471821 odd437Tree_30287 odd437Tree_30440
    rfl (by decide +kernel) odd437_sorted_30287 odd437_sorted_30440

theorem odd437_queries_30441 : odd437Tree_30441.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30441 [16] [12] 71197823471821 odd437Tree_30287 odd437Tree_30440
    rfl odd437_queries_30287 odd437_queries_30440

-- 77 source leaves.
theorem odd437_valid_30594 : odd437Tree_30594.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30594 : odd437Tree_30594.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30594 : odd437Tree_30594.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_30747 : odd437Tree_30747.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30747 : odd437Tree_30747.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30747 : odd437Tree_30747.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_30748 : odd437Tree_30748.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30748 [16] [] 46763884266151 odd437Tree_30594 odd437Tree_30747
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30594 odd437_valid_30747

theorem odd437_sorted_30748 : odd437Tree_30748.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30748 [16] [] 46763884266151 odd437Tree_30594 odd437Tree_30747
    rfl (by decide +kernel) odd437_sorted_30594 odd437_sorted_30747

theorem odd437_queries_30748 : odd437Tree_30748.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30748 [16] [] 46763884266151 odd437Tree_30594 odd437Tree_30747
    rfl odd437_queries_30594 odd437_queries_30747

-- 308 source leaves.
theorem odd437_valid_30749 : odd437Tree_30749.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30749 [16] [] 46763884266151 odd437Tree_30441 odd437Tree_30748
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30441 odd437_valid_30748

theorem odd437_sorted_30749 : odd437Tree_30749.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30749 [16] [] 46763884266151 odd437Tree_30441 odd437Tree_30748
    rfl (by decide +kernel) odd437_sorted_30441 odd437_sorted_30748

theorem odd437_queries_30749 : odd437Tree_30749.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30749 [16] [] 46763884266151 odd437Tree_30441 odd437Tree_30748
    rfl odd437_queries_30441 odd437_queries_30748

-- 615 source leaves.
theorem odd437_valid_30750 : odd437Tree_30750.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_30750 [16] [] 46763884266151 odd437Tree_30134 odd437Tree_30749
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30134 odd437_valid_30749

theorem odd437_sorted_30750 : odd437Tree_30750.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_30750 [16] [] 46763884266151 odd437Tree_30134 odd437Tree_30749
    rfl (by decide +kernel) odd437_sorted_30134 odd437_sorted_30749

theorem odd437_queries_30750 : odd437Tree_30750.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_30750 [16] [] 46763884266151 odd437Tree_30134 odd437Tree_30749
    rfl odd437_queries_30134 odd437_queries_30749

-- 76 source leaves.
theorem odd437_valid_30901 : odd437Tree_30901.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_30901 : odd437Tree_30901.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_30901 : odd437Tree_30901.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_31054 : odd437Tree_31054.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31054 : odd437Tree_31054.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31054 : odd437Tree_31054.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_31055 : odd437Tree_31055.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31055 [16] [19] 46354052029194 odd437Tree_30901 odd437Tree_31054
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30901 odd437_valid_31054

theorem odd437_sorted_31055 : odd437Tree_31055.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31055 [16] [19] 46354052029194 odd437Tree_30901 odd437Tree_31054
    rfl (by decide +kernel) odd437_sorted_30901 odd437_sorted_31054

theorem odd437_queries_31055 : odd437Tree_31055.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31055 [16] [19] 46354052029194 odd437Tree_30901 odd437Tree_31054
    rfl odd437_queries_30901 odd437_queries_31054

-- 77 source leaves.
theorem odd437_valid_31208 : odd437Tree_31208.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31208 : odd437Tree_31208.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31208 : odd437Tree_31208.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_31361 : odd437Tree_31361.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31361 : odd437Tree_31361.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31361 : odd437Tree_31361.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_31362 : odd437Tree_31362.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31362 [16] [19] 45750076812090 odd437Tree_31208 odd437Tree_31361
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31208 odd437_valid_31361

theorem odd437_sorted_31362 : odd437Tree_31362.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31362 [16] [19] 45750076812090 odd437Tree_31208 odd437Tree_31361
    rfl (by decide +kernel) odd437_sorted_31208 odd437_sorted_31361

theorem odd437_queries_31362 : odd437Tree_31362.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31362 [16] [19] 45750076812090 odd437Tree_31208 odd437Tree_31361
    rfl odd437_queries_31208 odd437_queries_31361

-- 307 source leaves.
theorem odd437_valid_31363 : odd437Tree_31363.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31363 [16] [19] 45750076812090 odd437Tree_31055 odd437Tree_31362
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31055 odd437_valid_31362

theorem odd437_sorted_31363 : odd437Tree_31363.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31363 [16] [19] 45750076812090 odd437Tree_31055 odd437Tree_31362
    rfl (by decide +kernel) odd437_sorted_31055 odd437_sorted_31362

theorem odd437_queries_31363 : odd437Tree_31363.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31363 [16] [19] 45750076812090 odd437Tree_31055 odd437Tree_31362
    rfl odd437_queries_31055 odd437_queries_31362

-- 77 source leaves.
theorem odd437_valid_31516 : odd437Tree_31516.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31516 : odd437Tree_31516.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31516 : odd437Tree_31516.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_31669 : odd437Tree_31669.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31669 : odd437Tree_31669.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31669 : odd437Tree_31669.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_31670 : odd437Tree_31670.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31670 [16] [19] 46443458967027 odd437Tree_31516 odd437Tree_31669
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31516 odd437_valid_31669

theorem odd437_sorted_31670 : odd437Tree_31670.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31670 [16] [19] 46443458967027 odd437Tree_31516 odd437Tree_31669
    rfl (by decide +kernel) odd437_sorted_31516 odd437_sorted_31669

theorem odd437_queries_31670 : odd437Tree_31670.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31670 [16] [19] 46443458967027 odd437Tree_31516 odd437Tree_31669
    rfl odd437_queries_31516 odd437_queries_31669

-- 77 source leaves.
theorem odd437_valid_31823 : odd437Tree_31823.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31823 : odd437Tree_31823.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31823 : odd437Tree_31823.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_31976 : odd437Tree_31976.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_31976 : odd437Tree_31976.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_31976 : odd437Tree_31976.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_31977 : odd437Tree_31977.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31977 [16] [19] 50102671749466 odd437Tree_31823 odd437Tree_31976
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31823 odd437_valid_31976

theorem odd437_sorted_31977 : odd437Tree_31977.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31977 [16] [19] 50102671749466 odd437Tree_31823 odd437Tree_31976
    rfl (by decide +kernel) odd437_sorted_31823 odd437_sorted_31976

theorem odd437_queries_31977 : odd437Tree_31977.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31977 [16] [19] 50102671749466 odd437Tree_31823 odd437Tree_31976
    rfl odd437_queries_31823 odd437_queries_31976

-- 308 source leaves.
theorem odd437_valid_31978 : odd437Tree_31978.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31978 [16] [19] 46443458967027 odd437Tree_31670 odd437Tree_31977
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31670 odd437_valid_31977

theorem odd437_sorted_31978 : odd437Tree_31978.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31978 [16] [19] 46443458967027 odd437Tree_31670 odd437Tree_31977
    rfl (by decide +kernel) odd437_sorted_31670 odd437_sorted_31977

theorem odd437_queries_31978 : odd437Tree_31978.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31978 [16] [19] 46443458967027 odd437Tree_31670 odd437Tree_31977
    rfl odd437_queries_31670 odd437_queries_31977

-- 615 source leaves.
theorem odd437_valid_31979 : odd437Tree_31979.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31979 [16] [19] 45750076812090 odd437Tree_31363 odd437Tree_31978
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31363 odd437_valid_31978

theorem odd437_sorted_31979 : odd437Tree_31979.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31979 [16] [19] 45750076812090 odd437Tree_31363 odd437Tree_31978
    rfl (by decide +kernel) odd437_sorted_31363 odd437_sorted_31978

theorem odd437_queries_31979 : odd437Tree_31979.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31979 [16] [19] 45750076812090 odd437Tree_31363 odd437Tree_31978
    rfl odd437_queries_31363 odd437_queries_31978

-- 1230 source leaves.
theorem odd437_valid_31980 : odd437Tree_31980.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_31980 [16] [] 45750076812090 odd437Tree_30750 odd437Tree_31979
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_30750 odd437_valid_31979

theorem odd437_sorted_31980 : odd437Tree_31980.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_31980 [16] [] 45750076812090 odd437Tree_30750 odd437Tree_31979
    rfl (by decide +kernel) odd437_sorted_30750 odd437_sorted_31979

theorem odd437_queries_31980 : odd437Tree_31980.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_31980 [16] [] 45750076812090 odd437Tree_30750 odd437Tree_31979
    rfl odd437_queries_30750 odd437_queries_31979

-- 76 source leaves.
theorem odd437_valid_32131 : odd437Tree_32131.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32131 : odd437Tree_32131.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32131 : odd437Tree_32131.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_32284 : odd437Tree_32284.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32284 : odd437Tree_32284.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32284 : odd437Tree_32284.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_32285 : odd437Tree_32285.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_32285 [16] [] 50371349753246 odd437Tree_32131 odd437Tree_32284
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32131 odd437_valid_32284

theorem odd437_sorted_32285 : odd437Tree_32285.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_32285 [16] [] 50371349753246 odd437Tree_32131 odd437Tree_32284
    rfl (by decide +kernel) odd437_sorted_32131 odd437_sorted_32284

theorem odd437_queries_32285 : odd437Tree_32285.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_32285 [16] [] 50371349753246 odd437Tree_32131 odd437Tree_32284
    rfl odd437_queries_32131 odd437_queries_32284

-- 77 source leaves.
theorem odd437_valid_32438 : odd437Tree_32438.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32438 : odd437Tree_32438.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32438 : odd437Tree_32438.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_32591 : odd437Tree_32591.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32591 : odd437Tree_32591.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32591 : odd437Tree_32591.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_32592 : odd437Tree_32592.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_32592 [16] [22] 56273588178873 odd437Tree_32438 odd437Tree_32591
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32438 odd437_valid_32591

theorem odd437_sorted_32592 : odd437Tree_32592.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_32592 [16] [22] 56273588178873 odd437Tree_32438 odd437Tree_32591
    rfl (by decide +kernel) odd437_sorted_32438 odd437_sorted_32591

theorem odd437_queries_32592 : odd437Tree_32592.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_32592 [16] [22] 56273588178873 odd437Tree_32438 odd437Tree_32591
    rfl odd437_queries_32438 odd437_queries_32591

-- 307 source leaves.
theorem odd437_valid_32593 : odd437Tree_32593.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_32593 [16] [] 50371349753246 odd437Tree_32285 odd437Tree_32592
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32285 odd437_valid_32592

theorem odd437_sorted_32593 : odd437Tree_32593.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_32593 [16] [] 50371349753246 odd437Tree_32285 odd437Tree_32592
    rfl (by decide +kernel) odd437_sorted_32285 odd437_sorted_32592

theorem odd437_queries_32593 : odd437Tree_32593.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_32593 [16] [] 50371349753246 odd437Tree_32285 odd437Tree_32592
    rfl odd437_queries_32285 odd437_queries_32592

-- 77 source leaves.
theorem odd437_valid_32746 : odd437Tree_32746.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32746 : odd437Tree_32746.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32746 : odd437Tree_32746.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_32899 : odd437Tree_32899.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_32899 : odd437Tree_32899.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_32899 : odd437Tree_32899.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_32900 : odd437Tree_32900.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_32900 [16] [22] 54553549847273 odd437Tree_32746 odd437Tree_32899
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32746 odd437_valid_32899

theorem odd437_sorted_32900 : odd437Tree_32900.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_32900 [16] [22] 54553549847273 odd437Tree_32746 odd437Tree_32899
    rfl (by decide +kernel) odd437_sorted_32746 odd437_sorted_32899

theorem odd437_queries_32900 : odd437Tree_32900.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_32900 [16] [22] 54553549847273 odd437Tree_32746 odd437Tree_32899
    rfl odd437_queries_32746 odd437_queries_32899

-- 77 source leaves.
theorem odd437_valid_33053 : odd437Tree_33053.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33053 : odd437Tree_33053.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33053 : odd437Tree_33053.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_33206 : odd437Tree_33206.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33206 : odd437Tree_33206.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33206 : odd437Tree_33206.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_33207 : odd437Tree_33207.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33207 [16] [22] 55898462348100 odd437Tree_33053 odd437Tree_33206
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33053 odd437_valid_33206

theorem odd437_sorted_33207 : odd437Tree_33207.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33207 [16] [22] 55898462348100 odd437Tree_33053 odd437Tree_33206
    rfl (by decide +kernel) odd437_sorted_33053 odd437_sorted_33206

theorem odd437_queries_33207 : odd437Tree_33207.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33207 [16] [22] 55898462348100 odd437Tree_33053 odd437Tree_33206
    rfl odd437_queries_33053 odd437_queries_33206

-- 308 source leaves.
theorem odd437_valid_33208 : odd437Tree_33208.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33208 [16] [22] 54553549847273 odd437Tree_32900 odd437Tree_33207
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32900 odd437_valid_33207

theorem odd437_sorted_33208 : odd437Tree_33208.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33208 [16] [22] 54553549847273 odd437Tree_32900 odd437Tree_33207
    rfl (by decide +kernel) odd437_sorted_32900 odd437_sorted_33207

theorem odd437_queries_33208 : odd437Tree_33208.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33208 [16] [22] 54553549847273 odd437Tree_32900 odd437Tree_33207
    rfl odd437_queries_32900 odd437_queries_33207

-- 615 source leaves.
theorem odd437_valid_33209 : odd437Tree_33209.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33209 [16] [] 50371349753246 odd437Tree_32593 odd437Tree_33208
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_32593 odd437_valid_33208

theorem odd437_sorted_33209 : odd437Tree_33209.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33209 [16] [] 50371349753246 odd437Tree_32593 odd437Tree_33208
    rfl (by decide +kernel) odd437_sorted_32593 odd437_sorted_33208

theorem odd437_queries_33209 : odd437Tree_33209.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33209 [16] [] 50371349753246 odd437Tree_32593 odd437Tree_33208
    rfl odd437_queries_32593 odd437_queries_33208

-- 76 source leaves.
theorem odd437_valid_33360 : odd437Tree_33360.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33360 : odd437Tree_33360.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33360 : odd437Tree_33360.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_33513 : odd437Tree_33513.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33513 : odd437Tree_33513.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33513 : odd437Tree_33513.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_33514 : odd437Tree_33514.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33514 [16] [22] 59169503432314 odd437Tree_33360 odd437Tree_33513
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33360 odd437_valid_33513

theorem odd437_sorted_33514 : odd437Tree_33514.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33514 [16] [22] 59169503432314 odd437Tree_33360 odd437Tree_33513
    rfl (by decide +kernel) odd437_sorted_33360 odd437_sorted_33513

theorem odd437_queries_33514 : odd437Tree_33514.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33514 [16] [22] 59169503432314 odd437Tree_33360 odd437Tree_33513
    rfl odd437_queries_33360 odd437_queries_33513

-- 77 source leaves.
theorem odd437_valid_33667 : odd437Tree_33667.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33667 : odd437Tree_33667.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33667 : odd437Tree_33667.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_33820 : odd437Tree_33820.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33820 : odd437Tree_33820.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33820 : odd437Tree_33820.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_33821 : odd437Tree_33821.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33821 [] [] 44318453685014 odd437Tree_33667 odd437Tree_33820
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33667 odd437_valid_33820

theorem odd437_sorted_33821 : odd437Tree_33821.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33821 [] [] 44318453685014 odd437Tree_33667 odd437Tree_33820
    rfl (by decide +kernel) odd437_sorted_33667 odd437_sorted_33820

theorem odd437_queries_33821 : odd437Tree_33821.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33821 [] [] 44318453685014 odd437Tree_33667 odd437Tree_33820
    rfl odd437_queries_33667 odd437_queries_33820

-- 307 source leaves.
theorem odd437_valid_33822 : odd437Tree_33822.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_33822 [] [] 44318453685014 odd437Tree_33514 odd437Tree_33821
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33514 odd437_valid_33821

theorem odd437_sorted_33822 : odd437Tree_33822.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_33822 [] [] 44318453685014 odd437Tree_33514 odd437Tree_33821
    rfl (by decide +kernel) odd437_sorted_33514 odd437_sorted_33821

theorem odd437_queries_33822 : odd437Tree_33822.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_33822 [] [] 44318453685014 odd437Tree_33514 odd437Tree_33821
    rfl odd437_queries_33514 odd437_queries_33821

-- 77 source leaves.
theorem odd437_valid_33975 : odd437Tree_33975.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_33975 : odd437Tree_33975.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_33975 : odd437Tree_33975.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_34128 : odd437Tree_34128.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34128 : odd437Tree_34128.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34128 : odd437Tree_34128.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_34129 : odd437Tree_34129.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34129 [17] [10] 45719143194578 odd437Tree_33975 odd437Tree_34128
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33975 odd437_valid_34128

theorem odd437_sorted_34129 : odd437Tree_34129.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34129 [17] [10] 45719143194578 odd437Tree_33975 odd437Tree_34128
    rfl (by decide +kernel) odd437_sorted_33975 odd437_sorted_34128

theorem odd437_queries_34129 : odd437Tree_34129.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34129 [17] [10] 45719143194578 odd437Tree_33975 odd437Tree_34128
    rfl odd437_queries_33975 odd437_queries_34128

-- 77 source leaves.
theorem odd437_valid_34282 : odd437Tree_34282.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34282 : odd437Tree_34282.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34282 : odd437Tree_34282.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_34435 : odd437Tree_34435.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34435 : odd437Tree_34435.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34435 : odd437Tree_34435.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_34436 : odd437Tree_34436.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34436 [17] [10] 45536078448245 odd437Tree_34282 odd437Tree_34435
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34282 odd437_valid_34435

theorem odd437_sorted_34436 : odd437Tree_34436.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34436 [17] [10] 45536078448245 odd437Tree_34282 odd437Tree_34435
    rfl (by decide +kernel) odd437_sorted_34282 odd437_sorted_34435

theorem odd437_queries_34436 : odd437Tree_34436.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34436 [17] [10] 45536078448245 odd437Tree_34282 odd437Tree_34435
    rfl odd437_queries_34282 odd437_queries_34435

-- 308 source leaves.
theorem odd437_valid_34437 : odd437Tree_34437.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34437 [17] [10] 45536078448245 odd437Tree_34129 odd437Tree_34436
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34129 odd437_valid_34436

theorem odd437_sorted_34437 : odd437Tree_34437.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34437 [17] [10] 45536078448245 odd437Tree_34129 odd437Tree_34436
    rfl (by decide +kernel) odd437_sorted_34129 odd437_sorted_34436

theorem odd437_queries_34437 : odd437Tree_34437.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34437 [17] [10] 45536078448245 odd437Tree_34129 odd437Tree_34436
    rfl odd437_queries_34129 odd437_queries_34436

-- 615 source leaves.
theorem odd437_valid_34438 : odd437Tree_34438.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34438 [] [] 44318453685014 odd437Tree_33822 odd437Tree_34437
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33822 odd437_valid_34437

theorem odd437_sorted_34438 : odd437Tree_34438.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34438 [] [] 44318453685014 odd437Tree_33822 odd437Tree_34437
    rfl (by decide +kernel) odd437_sorted_33822 odd437_sorted_34437

theorem odd437_queries_34438 : odd437Tree_34438.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34438 [] [] 44318453685014 odd437Tree_33822 odd437Tree_34437
    rfl odd437_queries_33822 odd437_queries_34437

-- 1230 source leaves.
theorem odd437_valid_34439 : odd437Tree_34439.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34439 [] [] 44318453685014 odd437Tree_33209 odd437Tree_34438
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_33209 odd437_valid_34438

theorem odd437_sorted_34439 : odd437Tree_34439.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34439 [] [] 44318453685014 odd437Tree_33209 odd437Tree_34438
    rfl (by decide +kernel) odd437_sorted_33209 odd437_sorted_34438

theorem odd437_queries_34439 : odd437Tree_34439.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34439 [] [] 44318453685014 odd437Tree_33209 odd437Tree_34438
    rfl odd437_queries_33209 odd437_queries_34438

-- 2460 source leaves.
theorem odd437_valid_34440 : odd437Tree_34440.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34440 [] [] 44318453685014 odd437Tree_31980 odd437Tree_34439
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_31980 odd437_valid_34439

theorem odd437_sorted_34440 : odd437Tree_34440.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34440 [] [] 44318453685014 odd437Tree_31980 odd437Tree_34439
    rfl (by decide +kernel) odd437_sorted_31980 odd437_sorted_34439

theorem odd437_queries_34440 : odd437Tree_34440.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34440 [] [] 44318453685014 odd437Tree_31980 odd437Tree_34439
    rfl odd437_queries_31980 odd437_queries_34439

-- 76 source leaves.
theorem odd437_valid_34591 : odd437Tree_34591.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34591 : odd437Tree_34591.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34591 : odd437Tree_34591.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_34744 : odd437Tree_34744.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34744 : odd437Tree_34744.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34744 : odd437Tree_34744.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_34745 : odd437Tree_34745.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_34745 [17] [10] 46312089706993 odd437Tree_34591 odd437Tree_34744
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34591 odd437_valid_34744

theorem odd437_sorted_34745 : odd437Tree_34745.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_34745 [17] [10] 46312089706993 odd437Tree_34591 odd437Tree_34744
    rfl (by decide +kernel) odd437_sorted_34591 odd437_sorted_34744

theorem odd437_queries_34745 : odd437Tree_34745.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_34745 [17] [10] 46312089706993 odd437Tree_34591 odd437Tree_34744
    rfl odd437_queries_34591 odd437_queries_34744

-- 77 source leaves.
theorem odd437_valid_34898 : odd437Tree_34898.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_34898 : odd437Tree_34898.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_34898 : odd437Tree_34898.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_35051 : odd437Tree_35051.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35051 : odd437Tree_35051.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35051 : odd437Tree_35051.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_35052 : odd437Tree_35052.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35052 [17] [] 50127967538895 odd437Tree_34898 odd437Tree_35051
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34898 odd437_valid_35051

theorem odd437_sorted_35052 : odd437Tree_35052.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35052 [17] [] 50127967538895 odd437Tree_34898 odd437Tree_35051
    rfl (by decide +kernel) odd437_sorted_34898 odd437_sorted_35051

theorem odd437_queries_35052 : odd437Tree_35052.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35052 [17] [] 50127967538895 odd437Tree_34898 odd437Tree_35051
    rfl odd437_queries_34898 odd437_queries_35051

-- 307 source leaves.
theorem odd437_valid_35053 : odd437Tree_35053.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35053 [17] [] 46312089706993 odd437Tree_34745 odd437Tree_35052
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34745 odd437_valid_35052

theorem odd437_sorted_35053 : odd437Tree_35053.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35053 [17] [] 46312089706993 odd437Tree_34745 odd437Tree_35052
    rfl (by decide +kernel) odd437_sorted_34745 odd437_sorted_35052

theorem odd437_queries_35053 : odd437Tree_35053.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35053 [17] [] 46312089706993 odd437Tree_34745 odd437Tree_35052
    rfl odd437_queries_34745 odd437_queries_35052

-- 77 source leaves.
theorem odd437_valid_35206 : odd437Tree_35206.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35206 : odd437Tree_35206.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35206 : odd437Tree_35206.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_35359 : odd437Tree_35359.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35359 : odd437Tree_35359.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35359 : odd437Tree_35359.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_35360 : odd437Tree_35360.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35360 [17] [12] 87720730705157 odd437Tree_35206 odd437Tree_35359
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35206 odd437_valid_35359

theorem odd437_sorted_35360 : odd437Tree_35360.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35360 [17] [12] 87720730705157 odd437Tree_35206 odd437Tree_35359
    rfl (by decide +kernel) odd437_sorted_35206 odd437_sorted_35359

theorem odd437_queries_35360 : odd437Tree_35360.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35360 [17] [12] 87720730705157 odd437Tree_35206 odd437Tree_35359
    rfl odd437_queries_35206 odd437_queries_35359

-- 77 source leaves.
theorem odd437_valid_35513 : odd437Tree_35513.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35513 : odd437Tree_35513.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35513 : odd437Tree_35513.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_35666 : odd437Tree_35666.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35666 : odd437Tree_35666.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35666 : odd437Tree_35666.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_35667 : odd437Tree_35667.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35667 [17] [12] 89543311556160 odd437Tree_35513 odd437Tree_35666
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35513 odd437_valid_35666

theorem odd437_sorted_35667 : odd437Tree_35667.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35667 [17] [12] 89543311556160 odd437Tree_35513 odd437Tree_35666
    rfl (by decide +kernel) odd437_sorted_35513 odd437_sorted_35666

theorem odd437_queries_35667 : odd437Tree_35667.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35667 [17] [12] 89543311556160 odd437Tree_35513 odd437Tree_35666
    rfl odd437_queries_35513 odd437_queries_35666

-- 308 source leaves.
theorem odd437_valid_35668 : odd437Tree_35668.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35668 [17] [12] 87720730705157 odd437Tree_35360 odd437Tree_35667
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35360 odd437_valid_35667

theorem odd437_sorted_35668 : odd437Tree_35668.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35668 [17] [12] 87720730705157 odd437Tree_35360 odd437Tree_35667
    rfl (by decide +kernel) odd437_sorted_35360 odd437_sorted_35667

theorem odd437_queries_35668 : odd437Tree_35668.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35668 [17] [12] 87720730705157 odd437Tree_35360 odd437Tree_35667
    rfl odd437_queries_35360 odd437_queries_35667

-- 615 source leaves.
theorem odd437_valid_35669 : odd437Tree_35669.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35669 [17] [] 46312089706993 odd437Tree_35053 odd437Tree_35668
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35053 odd437_valid_35668

theorem odd437_sorted_35669 : odd437Tree_35669.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35669 [17] [] 46312089706993 odd437Tree_35053 odd437Tree_35668
    rfl (by decide +kernel) odd437_sorted_35053 odd437_sorted_35668

theorem odd437_queries_35669 : odd437Tree_35669.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35669 [17] [] 46312089706993 odd437Tree_35053 odd437Tree_35668
    rfl odd437_queries_35053 odd437_queries_35668

-- 76 source leaves.
theorem odd437_valid_35820 : odd437Tree_35820.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35820 : odd437Tree_35820.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35820 : odd437Tree_35820.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_35973 : odd437Tree_35973.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_35973 : odd437Tree_35973.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_35973 : odd437Tree_35973.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_35974 : odd437Tree_35974.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_35974 [17] [12] 89459469195198 odd437Tree_35820 odd437Tree_35973
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35820 odd437_valid_35973

theorem odd437_sorted_35974 : odd437Tree_35974.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_35974 [17] [12] 89459469195198 odd437Tree_35820 odd437Tree_35973
    rfl (by decide +kernel) odd437_sorted_35820 odd437_sorted_35973

theorem odd437_queries_35974 : odd437Tree_35974.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_35974 [17] [12] 89459469195198 odd437Tree_35820 odd437Tree_35973
    rfl odd437_queries_35820 odd437_queries_35973

-- 77 source leaves.
theorem odd437_valid_36127 : odd437Tree_36127.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36127 : odd437Tree_36127.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36127 : odd437Tree_36127.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_36280 : odd437Tree_36280.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36280 : odd437Tree_36280.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36280 : odd437Tree_36280.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_36281 : odd437Tree_36281.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36281 [17] [12] 94801842743233 odd437Tree_36127 odd437Tree_36280
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36127 odd437_valid_36280

theorem odd437_sorted_36281 : odd437Tree_36281.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36281 [17] [12] 94801842743233 odd437Tree_36127 odd437Tree_36280
    rfl (by decide +kernel) odd437_sorted_36127 odd437_sorted_36280

theorem odd437_queries_36281 : odd437Tree_36281.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36281 [17] [12] 94801842743233 odd437Tree_36127 odd437Tree_36280
    rfl odd437_queries_36127 odd437_queries_36280

-- 307 source leaves.
theorem odd437_valid_36282 : odd437Tree_36282.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36282 [17] [12] 89459469195198 odd437Tree_35974 odd437Tree_36281
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35974 odd437_valid_36281

theorem odd437_sorted_36282 : odd437Tree_36282.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36282 [17] [12] 89459469195198 odd437Tree_35974 odd437Tree_36281
    rfl (by decide +kernel) odd437_sorted_35974 odd437_sorted_36281

theorem odd437_queries_36282 : odd437Tree_36282.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36282 [17] [12] 89459469195198 odd437Tree_35974 odd437Tree_36281
    rfl odd437_queries_35974 odd437_queries_36281

-- 77 source leaves.
theorem odd437_valid_36435 : odd437Tree_36435.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36435 : odd437Tree_36435.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36435 : odd437Tree_36435.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_36588 : odd437Tree_36588.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36588 : odd437Tree_36588.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36588 : odd437Tree_36588.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_36589 : odd437Tree_36589.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36589 [17] [] 55014392613746 odd437Tree_36435 odd437Tree_36588
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36435 odd437_valid_36588

theorem odd437_sorted_36589 : odd437Tree_36589.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36589 [17] [] 55014392613746 odd437Tree_36435 odd437Tree_36588
    rfl (by decide +kernel) odd437_sorted_36435 odd437_sorted_36588

theorem odd437_queries_36589 : odd437Tree_36589.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36589 [17] [] 55014392613746 odd437Tree_36435 odd437Tree_36588
    rfl odd437_queries_36435 odd437_queries_36588

-- 77 source leaves.
theorem odd437_valid_36742 : odd437Tree_36742.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36742 : odd437Tree_36742.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36742 : odd437Tree_36742.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_36895 : odd437Tree_36895.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_36895 : odd437Tree_36895.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_36895 : odd437Tree_36895.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_36896 : odd437Tree_36896.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36896 [17] [19] 55863907740136 odd437Tree_36742 odd437Tree_36895
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36742 odd437_valid_36895

theorem odd437_sorted_36896 : odd437Tree_36896.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36896 [17] [19] 55863907740136 odd437Tree_36742 odd437Tree_36895
    rfl (by decide +kernel) odd437_sorted_36742 odd437_sorted_36895

theorem odd437_queries_36896 : odd437Tree_36896.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36896 [17] [19] 55863907740136 odd437Tree_36742 odd437Tree_36895
    rfl odd437_queries_36742 odd437_queries_36895

-- 308 source leaves.
theorem odd437_valid_36897 : odd437Tree_36897.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36897 [17] [] 55014392613746 odd437Tree_36589 odd437Tree_36896
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36589 odd437_valid_36896

theorem odd437_sorted_36897 : odd437Tree_36897.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36897 [17] [] 55014392613746 odd437Tree_36589 odd437Tree_36896
    rfl (by decide +kernel) odd437_sorted_36589 odd437_sorted_36896

theorem odd437_queries_36897 : odd437Tree_36897.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36897 [17] [] 55014392613746 odd437Tree_36589 odd437Tree_36896
    rfl odd437_queries_36589 odd437_queries_36896

-- 615 source leaves.
theorem odd437_valid_36898 : odd437Tree_36898.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36898 [17] [] 55014392613746 odd437Tree_36282 odd437Tree_36897
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36282 odd437_valid_36897

theorem odd437_sorted_36898 : odd437Tree_36898.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36898 [17] [] 55014392613746 odd437Tree_36282 odd437Tree_36897
    rfl (by decide +kernel) odd437_sorted_36282 odd437_sorted_36897

theorem odd437_queries_36898 : odd437Tree_36898.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36898 [17] [] 55014392613746 odd437Tree_36282 odd437Tree_36897
    rfl odd437_queries_36282 odd437_queries_36897

-- 1230 source leaves.
theorem odd437_valid_36899 : odd437Tree_36899.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_36899 [17] [] 46312089706993 odd437Tree_35669 odd437Tree_36898
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_35669 odd437_valid_36898

theorem odd437_sorted_36899 : odd437Tree_36899.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_36899 [17] [] 46312089706993 odd437Tree_35669 odd437Tree_36898
    rfl (by decide +kernel) odd437_sorted_35669 odd437_sorted_36898

theorem odd437_queries_36899 : odd437Tree_36899.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_36899 [17] [] 46312089706993 odd437Tree_35669 odd437Tree_36898
    rfl odd437_queries_35669 odd437_queries_36898

-- 76 source leaves.
theorem odd437_valid_37050 : odd437Tree_37050.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37050 : odd437Tree_37050.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37050 : odd437Tree_37050.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_37203 : odd437Tree_37203.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37203 : odd437Tree_37203.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37203 : odd437Tree_37203.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 153 source leaves.
theorem odd437_valid_37204 : odd437Tree_37204.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_37204 [17] [19] 54298171791912 odd437Tree_37050 odd437Tree_37203
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37050 odd437_valid_37203

theorem odd437_sorted_37204 : odd437Tree_37204.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_37204 [17] [19] 54298171791912 odd437Tree_37050 odd437Tree_37203
    rfl (by decide +kernel) odd437_sorted_37050 odd437_sorted_37203

theorem odd437_queries_37204 : odd437Tree_37204.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_37204 [17] [19] 54298171791912 odd437Tree_37050 odd437Tree_37203
    rfl odd437_queries_37050 odd437_queries_37203

-- 77 source leaves.
theorem odd437_valid_37357 : odd437Tree_37357.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37357 : odd437Tree_37357.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37357 : odd437Tree_37357.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_37510 : odd437Tree_37510.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37510 : odd437Tree_37510.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37510 : odd437Tree_37510.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_37511 : odd437Tree_37511.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_37511 [17] [19] 55232300267242 odd437Tree_37357 odd437Tree_37510
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37357 odd437_valid_37510

theorem odd437_sorted_37511 : odd437Tree_37511.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_37511 [17] [19] 55232300267242 odd437Tree_37357 odd437Tree_37510
    rfl (by decide +kernel) odd437_sorted_37357 odd437_sorted_37510

theorem odd437_queries_37511 : odd437Tree_37511.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_37511 [17] [19] 55232300267242 odd437Tree_37357 odd437Tree_37510
    rfl odd437_queries_37357 odd437_queries_37510

-- 307 source leaves.
theorem odd437_valid_37512 : odd437Tree_37512.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_37512 [17] [19] 54298171791912 odd437Tree_37204 odd437Tree_37511
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37204 odd437_valid_37511

theorem odd437_sorted_37512 : odd437Tree_37512.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_37512 [17] [19] 54298171791912 odd437Tree_37204 odd437Tree_37511
    rfl (by decide +kernel) odd437_sorted_37204 odd437_sorted_37511

theorem odd437_queries_37512 : odd437Tree_37512.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_37512 [17] [19] 54298171791912 odd437Tree_37204 odd437Tree_37511
    rfl odd437_queries_37204 odd437_queries_37511

-- 77 source leaves.
theorem odd437_valid_37665 : odd437Tree_37665.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37665 : odd437Tree_37665.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37665 : odd437Tree_37665.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_37818 : odd437Tree_37818.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37818 : odd437Tree_37818.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37818 : odd437Tree_37818.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_37819 : odd437Tree_37819.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_37819 [17] [19] 58537072315610 odd437Tree_37665 odd437Tree_37818
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37665 odd437_valid_37818

theorem odd437_sorted_37819 : odd437Tree_37819.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_37819 [17] [19] 58537072315610 odd437Tree_37665 odd437Tree_37818
    rfl (by decide +kernel) odd437_sorted_37665 odd437_sorted_37818

theorem odd437_queries_37819 : odd437Tree_37819.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_37819 [17] [19] 58537072315610 odd437Tree_37665 odd437Tree_37818
    rfl odd437_queries_37665 odd437_queries_37818

-- 77 source leaves.
theorem odd437_valid_37972 : odd437Tree_37972.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_37972 : odd437Tree_37972.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_37972 : odd437Tree_37972.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_38125 : odd437Tree_38125.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38125 : odd437Tree_38125.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38125 : odd437Tree_38125.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_38126 : odd437Tree_38126.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38126 [17] [] 59418812627677 odd437Tree_37972 odd437Tree_38125
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37972 odd437_valid_38125

theorem odd437_sorted_38126 : odd437Tree_38126.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38126 [17] [] 59418812627677 odd437Tree_37972 odd437Tree_38125
    rfl (by decide +kernel) odd437_sorted_37972 odd437_sorted_38125

theorem odd437_queries_38126 : odd437Tree_38126.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38126 [17] [] 59418812627677 odd437Tree_37972 odd437Tree_38125
    rfl odd437_queries_37972 odd437_queries_38125

-- 308 source leaves.
theorem odd437_valid_38127 : odd437Tree_38127.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38127 [17] [] 58537072315610 odd437Tree_37819 odd437Tree_38126
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37819 odd437_valid_38126

theorem odd437_sorted_38127 : odd437Tree_38127.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38127 [17] [] 58537072315610 odd437Tree_37819 odd437Tree_38126
    rfl (by decide +kernel) odd437_sorted_37819 odd437_sorted_38126

theorem odd437_queries_38127 : odd437Tree_38127.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38127 [17] [] 58537072315610 odd437Tree_37819 odd437Tree_38126
    rfl odd437_queries_37819 odd437_queries_38126

-- 615 source leaves.
theorem odd437_valid_38128 : odd437Tree_38128.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38128 [17] [] 54298171791912 odd437Tree_37512 odd437Tree_38127
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_37512 odd437_valid_38127

theorem odd437_sorted_38128 : odd437Tree_38128.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38128 [17] [] 54298171791912 odd437Tree_37512 odd437Tree_38127
    rfl (by decide +kernel) odd437_sorted_37512 odd437_sorted_38127

theorem odd437_queries_38128 : odd437Tree_38128.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38128 [17] [] 54298171791912 odd437Tree_37512 odd437Tree_38127
    rfl odd437_queries_37512 odd437_queries_38127

-- 77 source leaves.
theorem odd437_valid_38281 : odd437Tree_38281.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38281 : odd437Tree_38281.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38281 : odd437Tree_38281.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_38434 : odd437Tree_38434.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38434 : odd437Tree_38434.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38434 : odd437Tree_38434.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_38435 : odd437Tree_38435.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38435 [17] [22] 67260025501503 odd437Tree_38281 odd437Tree_38434
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38281 odd437_valid_38434

theorem odd437_sorted_38435 : odd437Tree_38435.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38435 [17] [22] 67260025501503 odd437Tree_38281 odd437Tree_38434
    rfl (by decide +kernel) odd437_sorted_38281 odd437_sorted_38434

theorem odd437_queries_38435 : odd437Tree_38435.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38435 [17] [22] 67260025501503 odd437Tree_38281 odd437Tree_38434
    rfl odd437_queries_38281 odd437_queries_38434

-- 77 source leaves.
theorem odd437_valid_38588 : odd437Tree_38588.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38588 : odd437Tree_38588.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38588 : odd437Tree_38588.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_38741 : odd437Tree_38741.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38741 : odd437Tree_38741.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38741 : odd437Tree_38741.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_38742 : odd437Tree_38742.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38742 [17] [22] 63846092759024 odd437Tree_38588 odd437Tree_38741
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38588 odd437_valid_38741

theorem odd437_sorted_38742 : odd437Tree_38742.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38742 [17] [22] 63846092759024 odd437Tree_38588 odd437Tree_38741
    rfl (by decide +kernel) odd437_sorted_38588 odd437_sorted_38741

theorem odd437_queries_38742 : odd437Tree_38742.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38742 [17] [22] 63846092759024 odd437Tree_38588 odd437Tree_38741
    rfl odd437_queries_38588 odd437_queries_38741

-- 308 source leaves.
theorem odd437_valid_38743 : odd437Tree_38743.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_38743 [17] [22] 63846092759024 odd437Tree_38435 odd437Tree_38742
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38435 odd437_valid_38742

theorem odd437_sorted_38743 : odd437Tree_38743.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_38743 [17] [22] 63846092759024 odd437Tree_38435 odd437Tree_38742
    rfl (by decide +kernel) odd437_sorted_38435 odd437_sorted_38742

theorem odd437_queries_38743 : odd437Tree_38743.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_38743 [17] [22] 63846092759024 odd437Tree_38435 odd437Tree_38742
    rfl odd437_queries_38435 odd437_queries_38742

-- 77 source leaves.
theorem odd437_valid_38896 : odd437Tree_38896.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_38896 : odd437Tree_38896.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_38896 : odd437Tree_38896.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_39049 : odd437Tree_39049.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_39049 : odd437Tree_39049.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_39049 : odd437Tree_39049.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_39050 : odd437Tree_39050.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39050 [17] [22] 62209622262337 odd437Tree_38896 odd437Tree_39049
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38896 odd437_valid_39049

theorem odd437_sorted_39050 : odd437Tree_39050.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39050 [17] [22] 62209622262337 odd437Tree_38896 odd437Tree_39049
    rfl (by decide +kernel) odd437_sorted_38896 odd437_sorted_39049

theorem odd437_queries_39050 : odd437Tree_39050.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39050 [17] [22] 62209622262337 odd437Tree_38896 odd437Tree_39049
    rfl odd437_queries_38896 odd437_queries_39049

-- 77 source leaves.
theorem odd437_valid_39203 : odd437Tree_39203.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_39203 : odd437Tree_39203.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_39203 : odd437Tree_39203.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 77 source leaves.
theorem odd437_valid_39356 : odd437Tree_39356.Valid 19 23 3 100000118525840 := by
  decide +kernel

theorem odd437_sorted_39356 : odd437Tree_39356.Sorted odd437Key = true := by
  decide +kernel

theorem odd437_queries_39356 : odd437Tree_39356.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  decide +kernel

-- 154 source leaves.
theorem odd437_valid_39357 : odd437Tree_39357.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39357 [17] [22] 63921344194139 odd437Tree_39203 odd437Tree_39356
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_39203 odd437_valid_39356

theorem odd437_sorted_39357 : odd437Tree_39357.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39357 [17] [22] 63921344194139 odd437Tree_39203 odd437Tree_39356
    rfl (by decide +kernel) odd437_sorted_39203 odd437_sorted_39356

theorem odd437_queries_39357 : odd437Tree_39357.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39357 [17] [22] 63921344194139 odd437Tree_39203 odd437Tree_39356
    rfl odd437_queries_39203 odd437_queries_39356

-- 308 source leaves.
theorem odd437_valid_39358 : odd437Tree_39358.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39358 [17] [22] 62209622262337 odd437Tree_39050 odd437Tree_39357
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_39050 odd437_valid_39357

theorem odd437_sorted_39358 : odd437Tree_39358.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39358 [17] [22] 62209622262337 odd437Tree_39050 odd437Tree_39357
    rfl (by decide +kernel) odd437_sorted_39050 odd437_sorted_39357

theorem odd437_queries_39358 : odd437Tree_39358.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39358 [17] [22] 62209622262337 odd437Tree_39050 odd437Tree_39357
    rfl odd437_queries_39050 odd437_queries_39357

-- 616 source leaves.
theorem odd437_valid_39359 : odd437Tree_39359.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39359 [17] [22] 62209622262337 odd437Tree_38743 odd437Tree_39358
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38743 odd437_valid_39358

theorem odd437_sorted_39359 : odd437Tree_39359.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39359 [17] [22] 62209622262337 odd437Tree_38743 odd437Tree_39358
    rfl (by decide +kernel) odd437_sorted_38743 odd437_sorted_39358

theorem odd437_queries_39359 : odd437Tree_39359.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39359 [17] [22] 62209622262337 odd437Tree_38743 odd437Tree_39358
    rfl odd437_queries_38743 odd437_queries_39358

-- 1231 source leaves.
theorem odd437_valid_39360 : odd437Tree_39360.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39360 [17] [] 54298171791912 odd437Tree_38128 odd437Tree_39359
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_38128 odd437_valid_39359

theorem odd437_sorted_39360 : odd437Tree_39360.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39360 [17] [] 54298171791912 odd437Tree_38128 odd437Tree_39359
    rfl (by decide +kernel) odd437_sorted_38128 odd437_sorted_39359

theorem odd437_queries_39360 : odd437Tree_39360.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39360 [17] [] 54298171791912 odd437Tree_38128 odd437Tree_39359
    rfl odd437_queries_38128 odd437_queries_39359

-- 2461 source leaves.
theorem odd437_valid_39361 : odd437Tree_39361.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39361 [17] [] 46312089706993 odd437Tree_36899 odd437Tree_39360
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_36899 odd437_valid_39360

theorem odd437_sorted_39361 : odd437Tree_39361.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39361 [17] [] 46312089706993 odd437Tree_36899 odd437Tree_39360
    rfl (by decide +kernel) odd437_sorted_36899 odd437_sorted_39360

theorem odd437_queries_39361 : odd437Tree_39361.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39361 [17] [] 46312089706993 odd437Tree_36899 odd437Tree_39360
    rfl odd437_queries_36899 odd437_queries_39360

-- 4921 source leaves.
theorem odd437_valid_39362 : odd437Tree_39362.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39362 [] [] 44318453685014 odd437Tree_34440 odd437Tree_39361
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_34440 odd437_valid_39361

theorem odd437_sorted_39362 : odd437Tree_39362.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39362 [] [] 44318453685014 odd437Tree_34440 odd437Tree_39361
    rfl (by decide +kernel) odd437_sorted_34440 odd437_sorted_39361

theorem odd437_queries_39362 : odd437Tree_39362.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39362 [] [] 44318453685014 odd437Tree_34440 odd437Tree_39361
    rfl odd437_queries_34440 odd437_queries_39361

-- 9842 source leaves.
theorem odd437_valid_39363 : odd437Tree_39363.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39363 [] [] 4001691700794 odd437Tree_29521 odd437Tree_39362
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_29521 odd437_valid_39362

theorem odd437_sorted_39363 : odd437Tree_39363.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39363 [] [] 4001691700794 odd437Tree_29521 odd437Tree_39362
    rfl (by decide +kernel) odd437_sorted_29521 odd437_sorted_39362

theorem odd437_queries_39363 : odd437Tree_39363.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39363 [] [] 4001691700794 odd437Tree_29521 odd437Tree_39362
    rfl odd437_queries_29521 odd437_queries_39362

-- 19683 source leaves.
theorem odd437_valid_39364 : odd437Tree_39364.Valid 19 23 3 100000118525840 := by
  exact PairCertificateTree.valid_of_branch_eq 19 23 3 100000118525840 odd437Tree_39364 [] [] 0 odd437Tree_19680 odd437Tree_39363
    rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    odd437_valid_19680 odd437_valid_39363

theorem odd437_sorted_39364 : odd437Tree_39364.Sorted odd437Key = true := by
  exact PairCertificateTree.sorted_of_branch_eq odd437Key odd437Tree_39364 [] [] 0 odd437Tree_19680 odd437Tree_39363
    rfl (by decide +kernel) odd437_sorted_19680 odd437_sorted_39363

theorem odd437_queries_39364 : odd437Tree_39364.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true := by
  exact PairCertificateTree.rows_all_of_branch_eq (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) odd437Tree_39364 [] [] 0 odd437Tree_19680 odd437Tree_39363
    rfl odd437_queries_19680 odd437_queries_39363

theorem odd437_tree_valid : odd437Tree.Valid 19 23 3 100000118525840 :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.Valid 19 23 3 100000118525840) (show odd437Tree = odd437Tree_39364 from rfl)) odd437_valid_39364

theorem odd437_tree_sorted : odd437Tree.Sorted odd437Key = true :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.Sorted odd437Key = true) (show odd437Tree = odd437Tree_39364 from rfl)) odd437_sorted_39364

theorem odd437_tree_queries : odd437Tree.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true :=
  Eq.mpr (congrArg (fun t : PairCertificateTree => t.rows.all (fun source => odd437Tree.FastQuery 2 19 23 199410 340830 source) = true) (show odd437Tree = odd437Tree_39364 from rfl)) odd437_queries_39364

theorem odd437_tree_geometry : odd437Tree.GeometryValid 2 19 23 = true :=
  PairCertificateTree.fastGeometryValid_sound 2 19 23 199410 340830 (by decide) (by decide)
    odd437_pMask odd437_qMask odd437Tree
    (PairCertificateTree.fastGeometry_of_rows_all 2 19 23 199410 340830 odd437Tree odd437_tree_queries)

end NK.Certificates
