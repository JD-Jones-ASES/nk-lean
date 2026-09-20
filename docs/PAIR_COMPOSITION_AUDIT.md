# Retained-pair certificate composition audit

The new module `NK/PairCertificateComposition.lean` is the only repository file edited in this increment. It builds without warnings. No existing checker, data file, or mathematical statement was changed.

All public lemmas are in `NK.PairCertificateTree`:

- `valid_of_branch_eq p q e D t a b s l r hshape hpLeft hpRight hqLeft hqRight hminLeft hminRight hValidLeft hValidRight` assembles validity from six summary facts and two child proofs.
- `sorted_of_branch_eq key t a b s l r hshape hgap hSortedLeft hSortedRight` assembles sortedness from the child boundary key gap and child proofs.
- `rows_all_of_branch_eq test t a b s l r hshape hAllLeft hAllRight` assembles an arbitrary, identical Boolean test across both source-row lists.
- `rows_all_of_eq test t u hshape h` transports the source-row check across a tree alias.
- `fastGeometry_of_rows_all k p q pMask qMask t h` packages the assembled literal global-query predicate as `FastGeometryValid` without reducing the full source list.

The branch lemmas use `hshape : t = .branch a b s l r`; alias transport uses `hshape : t = u`. The row-test argument is fixed and opaque in the generic proof. For geometry it must query each source against the same full target tree. Child-local geometry checks cannot replace these hypotheses, because they omit cross-child arcs.

Exact controls in `/private/tmp/nk-pair-composition-controls.lean` pass for valid parent assembly, sortedness, source partition, alias transport, and final geometry packaging. Negative controls reject a false prefix summary, false minimum-start summary, reversed key gap, and a false row test. A substantive cross-child control has both singleton child-local geometry checks true, but rejects their overlapping parent and rejects the corresponding source chunk queried against that full parent. This confirms the required scope of the shared row test.

Axiom printouts: `valid_of_branch_eq`, `sorted_of_branch_eq`, `rows_all_of_branch_eq`, and `fastGeometry_of_rows_all` depend only on `propext`; `rows_all_of_eq` is axiom-free. `git diff --check` passes. No large certificate was launched and no Lean process remains in this lane.
