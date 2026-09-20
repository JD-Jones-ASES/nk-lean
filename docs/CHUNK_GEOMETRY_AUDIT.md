# Chunked geometry review

This AI-assisted review checks how literal odd-component data are divided
into smaller Lean proofs and assembled into full geometry theorems. Python
controls test the generators; they are not proof oracles. The accepted
official replay is recorded in [VERIFICATION.md](VERIFICATION.md).

## Data and coverage

| Component | Primes | Denominator | Rows | Directly checked chunks | Rows per chunk | Assembled parents |
| --- | --- | ---: | ---: | ---: | --- | ---: |
| 215 | 5, 43 | 99999974386028 | 4913 | 64 | 76 or 77 | 63 |
| 437 | 19, 23 | 100000118525840 | 19683 | 256 | 76 or 77 | 255 |

Every leaf tuple contains two length-three words, a start, and a width. The
frontier partitions the literal rows exactly once and agrees with the flat
certificate data. The checks cover word uniqueness, strict mixed-radix key
order, row bounds, internal common prefixes, minimum-start bounds, and
child-boundary key gaps. Each named tree body and root alias must match a
reconstruction from the flat input, with no missing or repeated declarations.

## Query and assembly scope

Each source chunk is queried against the same full target tree. Only the
source rows are partitioned. Replacing the target with a child subtree would
omit cross-child arcs and is not justified.

The parent proofs in
[PairCertificateComposition.lean](../NK/PairCertificateComposition.lean)
preserve that fixed global query. Validity requires six local summary facts
and both child validity proofs. Sortedness requires the strict boundary gap
and both child sortedness proofs. The generic row lemma combines
`List.all` over append with an arbitrary fixed Boolean predicate.
Tree-shape equalities connect these applications to the literal data.

The final soundness theorem receives the actual primes, exponent 2, and
checked nonzero-square masks. Generic assembly uses already proved child
predicates; this source-level observation is not an asymptotic performance
claim.

## Generator controls

[generate_chunked_odd_geometry.py](../scripts/generate_chunked_odd_geometry.py)
compares complete tree bodies and the root alias before writing output.
Mismatches raise explicit exceptions, including under Python optimization.
The main [geometry generator](../scripts/generate_odd_geometry.py) writes
the final chunked Geometry file once. Serial elaboration changes proof
scheduling only.

The [control driver](../scripts/check_chunk_geometry_generator.py) intercepts
writes and checks standalone and main-generation output. Its main-routing
test stubs the costly Python geometry visit counter, so that test establishes
deterministic generation and write routing, not a fresh literal geometry
replay.

For each component, all seven mutations are rejected before any output write:

- Change a width in an imported tree body.
- Remove a named node.
- Duplicate a named node.
- Add an unexpected named node.
- Point the root alias at the wrong subtree.
- Duplicate the root alias.
- Change a flat-input width while retaining the corresponding old Data file.

Normal and optimized Python exercise the same controls and produce identical
generated output. From the repository root:

```sh
python3 scripts/check_chunk_geometry_generator.py
python3 -O scripts/check_chunk_geometry_generator.py
```

The driver starts no Lean process and rewrites no certificate data. Lean
checks the resulting literal geometry statements; generator success alone
does not establish them.
