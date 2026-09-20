# Verification, 20 September 2026

**The complete official Comparator run passed** on proof commit
409bcef149ae96f40f69d38a17cf8bd7330dee98. Statement and ordinary-definition matching,
the standard-axiom policy, Lean default-kernel replay and NanoDa all accepted.
The run exited zero with its final success message after 2777.40 seconds.

The same single master configuration selected all 19 statements; no subset
replays, definition holes, enlarged axiom list or modified checker were used.
This was developer-controlled source replay on macOS using the official
unsandboxed Landrun shim. It is not the separate Palomar Linux intake gate.

- Full replay log: [comparator-409bcef.log](replay/comparator-409bcef.log).
- Run metadata: [comparator-409bcef.json](replay/comparator-409bcef.json).
- Log SHA256: 55b8007b6deb5185cf708e4cdf5998decb61700cf9f4e87c7bfd7a591a5f0a23.
- Full Solution export: 232,434,222 bytes; SHA256
  e12be5029a582cad015d4e0e4fef200e0b31fdcd1b0c16651f710233a544cc71.
- Export provenance: [solution-export-409bcef.json](replay/solution-export-409bcef.json).
- All 118 source/build/certificate input hashes:
  [proof-inputs-409bcef.json](replay/proof-inputs-409bcef.json).
- Complete development audit log:
  [development-audit-409bcef.log](replay/development-audit-409bcef.log).

The later packaging checkpoint changes documentation and verification records,
not these proof inputs or the compared statements. The accepted run is attributed
to the exact proof commit above; it is not relabeled as a separate run on a
documentation-only commit. REPLAY_TOOLCHAIN.md pins all tools and gives the
replay command.

## Complete Lean development checks

The full `lake build` passes with Lean 4.33.0 and the committed Mathlib/rk-lean
pins. It compiles NK, Challenge, Solution and Audit. All three unconditional
all-N applications are proved: squares at 0.75806770413, fourth powers at
0.9142 and sixth powers at 0.95295. The square modulus at binary depth 10^15
remains symbolic; no enormous integer expansion is required.

The transitive audit checks **11,314 NK declarations**, including required
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
| Odd215 numerical moment, chunked | passed | 77 s |
| Odd215 actual component after numeric chunking | passed | 7.6 s |
| Odd437 numerical moment | passed | 188 s |
| Odd437 geometry | passed | 927 s |
| Odd437 actual component | passed | 6.4 s |
| SquareApplication after numeric chunking | passed | 5.2 s |

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

## Resource diagnosis and corrected proof representation

The earlier run at 99de2ade1fe572407d0295481b36f07167fa9e2e passed comparison,
the axiom policy and Lean replay, but NanoDa was killed. A logging-only diagnostic
copy subsequently confirmed attempted computation of 4^(10^15) in a binary
component proof. Chunking the Odd215 numerical proof alone did not resolve it.

The accepted candidate proves that a noncomputing chosen depth equals exactly
10^15, and uses that depth inside natural powers. Its scalar logarithmic
certificate and all mathematical conclusions are unchanged. The remedy passed
the unchanged official checker; the diagnostic checker was not used as the
acceptance authority. NANODA_POWER_REDUCTION.md retains the failed-run and
diagnostic evidence, including their precise limits.

The repository remains private. Public release, submission and registration
have not occurred and are separate from this mathematical verification.
