# Verification, 20 September 2026

## Complete Lean development checks

The full `lake build` passes with Lean 4.33.0 and the committed Mathlib/rk-lean
pins. It compiles NK, Challenge, Solution and Audit. All three unconditional
all-N applications are proved: squares at 0.75806770413, fourth powers at
0.9142 and sixth powers at 0.95295. The square modulus at binary depth 10^15
remains symbolic; no enormous integer expansion is required.

The transitive audit checks **10,794 NK declarations**, including required
headline names, and allows only `propext`, `Classical.choice` and `Quot.sound`.
Separate axiom reports for all three numerical bounds give the same list.
The source guard checks 70 proof files, with no prohibited tokens, Challenge
imports in proofs, or definition holes. It is supplementary to kernel replay.

`scripts/audit.sh` passes, including all 25 saved Lean control files. The controls
cover transfer/interpolation, zero widths, false numerical endpoints, dyadic
range conditions, binary geometry, tree summaries and cross-child queries,
residue masks, closure, graph products, empty/looped graphs, and the binary
prime-conductor exception. An earlier out-of-tree custom-axiom mutation was
rejected by the declaration audit. Two minor test-file lint cleanups were
replayed separately and passed warning-free before freezing the candidate;
they change no library declaration.

Challenge deliberately has 19 theorem placeholders and complete ordinary
mathematical definitions. Its 19 placeholder warnings are expected. Solution
does not import Challenge and has no admissions. `comparator.json` selects
19 theorem names, keeps `definition_names` empty and enables NanoDa.

## Exact finite certificates

| Final production check | Outcome | Observed build time |
|---|---|---:|
| Odd215 geometry, serial elaboration | passed | 173 s |
| Odd215 actual component | passed | 4.9 s |
| Odd437 numerical moment | passed | 188 s |
| Odd437 geometry | passed | 927 s |
| Odd437 actual component | passed | 6.4 s |
| SquareApplication, warning-free | passed | 4.0 s |

These are development timings on this host, not performance guarantees.
The actual 25-state/94-branch binary policy, all weighted growth inequalities,
finite-depth logarithmic certificate and actual binary MomentComponent also
compile and pass the standard-axiom audit. The 18 fourth/sixth seed geometries
and their exact moment certificates are included in the full build.

The geometry checker has a proved refinement to the original full-arc
condition. Its chunking partitions sources only; every source still queries
the complete target tree. Python normal/optimized modes reproduce the generated
geometry deterministically and reject 14 data/tree corruptions. The numerical
generator likewise reproduces the production source exactly in both modes and
rejects altered literal widths, flat widths and root aliases. These generator
controls are reproducibility evidence, not substitutes for the Lean proofs.
See CHUNK_GEOMETRY_AUDIT.md, NUMERIC_GENERATOR_AUDIT.json and CERTIFICATE_REPLAY.md.

Earlier monolithic numerical/geometry runs were stopped for memory pressure;
a sampled geometry process reached 12.8 GB. This was a resource limitation,
not a failed mathematical certificate. Bounded proof obligations, generic
assembly and serial theorem elaboration gave the successful production runs.
No axiom policy, endpoint, data row or mathematical hypothesis was weakened.

## Review and metadata

Distinct agents reviewed statement/definition fidelity, exact square assembly,
prime structure, and generator coverage. The review reports state their scope;
agent review is not human peer review or source-author endorsement. The final
symbolic coprimality helper was separately reviewed. Unit conductors and exact
prime-block/lexicographic capacities have their own boundary and negative
controls. Stronger Bellman/factor-two claims remain outside the 19 statements.

`formalization.yaml` passes the official upstream v0.4 schema with PyYAML 6.0.3
and jsonschema 4.26.0. Python compilation and `git diff --check` pass. The
metadata's zero-sorry counts refer to the proof-bearing Solution closure.

## Independent candidate replay

The official Comparator/Lean/NanoDa installation smoke test passed on its
`simple_match` control. The complete nk-lean comparison and independent replay
are the remaining verification gate and must identify the exact candidate
commit. REPLAY_TOOLCHAIN.md pins all tools and gives the command. On this
macOS host the official development Landrun shim provides no sandbox; a local
run is developer-controlled source replay, distinct from Palomar's Linux gate.

The repository remains private. Public release, submission and registration
have not occurred and are separate from mathematical verification.
