# Retained-pair composition review

[PairCertificateComposition.lean](../NK/PairCertificateComposition.lean)
assembles proofs about smaller trees into proofs about their parent.
This AI-assisted review concerns the generic assembly interface and its
controls. The accepted official replay appears in
[VERIFICATION.md](VERIFICATION.md).

## Proof interface

The public lemmas lie in `NK.PairCertificateTree`:

- `valid_of_branch_eq` requires six local summary facts and both child
  validity proofs.
- `sorted_of_branch_eq` requires a strict child-boundary key gap and both
  child sortedness proofs.
- `rows_all_of_branch_eq` combines the same arbitrary Boolean test over
  both source-row lists.
- `rows_all_of_eq` transports a source-row check across a tree alias.
- `fastGeometry_of_rows_all` packages the assembled global-query predicate
  as `FastGeometryValid`.

The branch lemmas use an equality `t = .branch a b s l r`; alias transport
uses `t = u`. The row predicate is fixed throughout the generic proof.
For geometry, every source must be queried against the same full target
tree. Child-local geometry omits cross-child arcs and cannot replace this
hypothesis.

## Controls and axioms

[audit/pair-composition-controls.lean](../audit/pair-composition-controls.lean)
checks parent validity, sortedness, source partition, alias transport, and
geometry packaging. Negative controls reject a false prefix summary, a false
minimum-start summary, a reversed key gap, and a false row predicate.

The cross-child control is substantive: both singleton children pass their
own geometry checks, while their overlapping parent fails. Querying the
source chunk against that full parent also fails. This tests the required
global target scope.

The axiom reports for `valid_of_branch_eq`, `sorted_of_branch_eq`,
`rows_all_of_branch_eq`, and `fastGeometry_of_rows_all` contain only
`propext`; `rows_all_of_eq` is axiom-free.

```sh
lake build NK.PairCertificateComposition
lake env lean audit/pair-composition-controls.lean
```
