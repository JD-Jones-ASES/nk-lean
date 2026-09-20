import NK.FastPairCertificate

/-! # Compositional assembly of retained-pair certificates

Named child certificates can be checked separately and assembled through these
lemmas. The shape equality exposes only one parent node. In particular,
`rows_all_of_branch_eq` treats the row test as an arbitrary function and never
unfolds or reevaluates a query against a fixed full target tree.
-/

namespace NK.PairCertificateTree

/-- Assemble validity from the six parent-summary facts and valid children. -/
theorem valid_of_branch_eq (p q e D : ℕ) (t : PairCertificateTree)
    (a b : List ℕ) (s : ℕ) (l r : PairCertificateTree)
    (hshape : t = .branch a b s l r)
    (hpLeft : CertificateWordPrefix a l.pPrefix)
    (hpRight : CertificateWordPrefix a r.pPrefix)
    (hqLeft : CertificateWordPrefix b l.qPrefix)
    (hqRight : CertificateWordPrefix b r.qPrefix)
    (hminLeft : s ≤ l.minStart) (hminRight : s ≤ r.minStart)
    (hValidLeft : l.Valid p q e D) (hValidRight : r.Valid p q e D) :
    t.Valid p q e D := by
  rw [hshape]
  exact ⟨hpLeft, hpRight, hqLeft, hqRight, hminLeft, hminRight,
    hValidLeft, hValidRight⟩

/-- Assemble sortedness from the single boundary gap and sorted children. -/
theorem sorted_of_branch_eq (key : RetainedPair → ℕ) (t : PairCertificateTree)
    (a b : List ℕ) (s : ℕ) (l r : PairCertificateTree)
    (hshape : t = .branch a b s l r)
    (hgap : key l.lastWord < key r.firstWord)
    (hSortedLeft : l.Sorted key = true) (hSortedRight : r.Sorted key = true) :
    t.Sorted key = true := by
  rw [hshape]
  simp only [Sorted, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hgap, hSortedLeft⟩, hSortedRight⟩

/-- Assemble checks over source rows while keeping their common test opaque.
For geometry, `test` can query each source against one fixed full target tree;
the two child checks must use precisely that same test. -/
theorem rows_all_of_branch_eq (test : PairCertificateRow → Bool) (t : PairCertificateTree)
    (a b : List ℕ) (s : ℕ) (l r : PairCertificateTree)
    (hshape : t = .branch a b s l r)
    (hAllLeft : l.rows.all test = true) (hAllRight : r.rows.all test = true) :
    t.rows.all test = true := by
  rw [hshape, rows, List.all_append, hAllLeft, hAllRight]
  rfl

/-- Transport a checked row predicate across a named tree alias. -/
theorem rows_all_of_eq (test : PairCertificateRow → Bool) (t u : PairCertificateTree)
    (hshape : t = u) (h : u.rows.all test = true) : t.rows.all test = true := by
  rw [hshape]
  exact h

/-- Package an assembled global-query row check without reducing the root list. -/
theorem fastGeometry_of_rows_all (k p q pMask qMask : ℕ) (t : PairCertificateTree)
    (h : t.rows.all (fun s => t.FastQuery k p q pMask qMask s) = true) :
    t.FastGeometryValid k p q pMask qMask = true := h

end NK.PairCertificateTree
