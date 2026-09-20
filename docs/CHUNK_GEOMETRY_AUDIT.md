# Chunked odd geometry generator review

**Result: PASS for the current generated inputs and assembly structure.** The initial audit was read-only; the follow-up strengthened generator freshness checks and removed the transient monolithic geometry write. No Lean process ran in this audit lane. Kernel replay and memory measurements belong to the separate build evidence.

## Exact coverage and parameters

| q | primes | denominator | source rows | directly checked chunks | chunk sizes | assembled parents |
|---|---|---:|---:|---:|---|---:|
| 215 | 5, 43 | 99999974386028 | 4913 | 64 | [76, 77] | 63 |
| 437 | 19, 23 | 100000118525840 | 19683 | 256 | [76, 77] | 255 |

All literal leaf tuples, including both length-3 words, starts and widths, occur exactly once across the frontier and agree as a multiset with the authoritative flat file. Word uniqueness, strict mixed-radix key order, row bounds, every internal common prefix and minimum-start bound, and every child-boundary key gap were independently checked. Every named data body and root alias matches an independent reconstruction; this strengthened the initial generator’s name-only freshness check, and the production generator now performs the same literal-body check.

## Full-target query scope

Every directly checked source chunk uses the predicate `fun source => oddQTree.FastQuery 2 p r pMask qMask source`, with the same full original `oddQTree`. There is no subtree target substitution. Parent `rows_all_of_branch_eq` applications use exactly that predicate and the literal left/right child theorem names. Thus the frontier partitions sources only; targets remain global. All parent query, validity and sortedness links were checked against their actual data-node shapes. Root aliases and final `fastGeometryValid_sound` arguments match the flat primes, square exponent, and computed nonzero-square masks.

## Generic assembly review

`PairCertificateComposition.valid_of_branch_eq` asks for all six local summary facts and both child Valid facts. `sorted_of_branch_eq` requires the strict boundary gap and both child Sorted facts. `rows_all_of_branch_eq` proves List.all over append for an arbitrary opaque predicate, so its proof is established with symbolic trees/test and does not reevaluate a closed full-tree query when instantiated. Parent `rfl` checks only literal tree shape. The parent boundary decision follows first/last paths; local summary decisions read child summaries. Final root transport and `fastGeometry_of_rows_all` use already proved predicates. This source inspection finds no reason for parent assembly to reintroduce monolithic query evaluation, but runtime memory behavior remains unmeasured here.

## Guard hardening and regeneration

The chunked geometry generator now reconstructs and compares every named tree body with the literal flat input, verifies the complete declaration list without duplicates, and requires exactly the correct root alias. Name-only freshness checking has been removed. Mismatches raise explicit `ValueError` exceptions before any output write; they remain checked under Python `-O`.

The main `generate_odd_geometry.py --q Q --emit` path no longer writes a temporary monolithic Geometry file. Its final chunk-generation call is the only Geometry write. The retained Data and successful Geometry output are mathematically unchanged. The separately coordinated `set_option Elab.async false` line is preserved in the generated wrapper to serialize elaboration; it does not alter theorem statements.

Both standalone chunk generation and the documented main generation path were exercised with `Path.write_text` intercepted in memory. For Q=215 and437, final Data bytes match the current files exactly, and final Geometry bytes match after ignoring only the separately added `Elab.async` line. Main generation's costly Python geometry visit counter was replaced by a zero-returning stub during this routing check; this was a determinism and write-routing test, not a new geometry search. Each main run performed exactly one captured Geometry write, with chunked content.

The separate numerical regeneration script now replaces both Odd215Numeric and Odd437Numeric with chunked moment wrappers. This changes only numerical proof boundaries and does not affect geometry chunking.

## Python controls

All controls passed in normal Python and `python3 -O`, with identical generated Lean hashes between modes. For each of215 and437, all seven mutations were rejected before any output write:

- Change a width in an imported literal tree body.
- Remove a named node.
- Duplicate a named node.
- Add an unexpected named node.
- Point the root alias at the wrong subtree.
- Duplicate the root alias.
- Change a width in the flat input while retaining the old Data file.

Generated Geometry SHA-256, including the serial-elaboration option:

- Odd215Geometry: `213d248c68204cfc3e951016d33c5be8b7a980d2d115cc85631b3e215cced245`
- Odd437Geometry: `2253476a07419212bff09b4a451ba00b4fd24f1b97c28cd97793320ff704717a`

The audit test used explicit exceptions, not Python assertions. No Lean builds were started by these controls, and all generator output writes during testing were intercepted. The portable audit driver is `scripts/check_chunk_geometry_generator.py`; it locates the repository from its own path. It is an audit convenience, not part of the mathematical proof boundary.

Rerun from the repository root:

```bash
python3 scripts/check_chunk_geometry_generator.py
```

The same controls were also exercised with Python `-O`. The driver intercepts generator writes and does not start Lean or rewrite certificate data.

## Source snapshot

- `scripts/check_chunk_geometry_generator.py`: `de569c955676493659c542d107eb7d4144d7687b413f35a5a3b491bdbfc2bf01`
- `scripts/generate_chunked_odd_geometry.py`: `a73d57efc86526450e43ef134697728046c311f2f0a98fd4baddbe065848d813`
- `scripts/generate_odd_geometry.py`: `fb878c50a777f484e10895b642dc285785b2839cb817c5df5fffdd2b2dba4e7c`
- `NK/PairCertificateComposition.lean`: `89b249233c1242abbf3ea0eae9287bdcbe7c59819e0c322fa62ab08435ce8644`
- `NK/FastPairCertificate.lean`: `a1835c0deae5d0e432d24ac83abc35e20454f361ee9b3f28f3bc91b59765d701`
- `NK/RetainedPairCertificate.lean`: `0c01fa45a0c35ddb14c3f3918ccf85eb42a8af79c2211ae20e82e7331bb14b3c`
- `NK/Certificates/Odd215Data.lean`: `2d90d7381b9f9999045e6c4de8c9eb861fcb9705ab7c67eac0592181ecd107b4`
- `NK/Certificates/Odd437Data.lean`: `d9e417efa20fa4d23b4a2ae1d284f9c2430d4656aaced0088aab192a43a323d5`
- `certificates/square/data/odd215.txt`: `1ae65e9349a66e184c4376dd4196253d0abb32d3a0d0fc2dc265f7a273d4abd6`
- `certificates/square/data/odd437.txt`: `fe026c70694a85892a749ea4417199325eb39ba79307c6351aa8de433585ffc0`

The generator remains untrusted. Lean checks the literal geometry claims; Python audit success does not substitute for that replay.
