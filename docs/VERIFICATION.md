# Development verification, 20 September 2026

The general interval-moment transfer, canonical closure, stopping-word and CRT
constructions, exact numerical evaluator, 18 even seed geometries and moments,
and the unconditional fourth/sixth all-N applications compile with the pinned
Lean4.33.0/Mathlib toolchain. `scripts/audit.sh` passed, including the complete
imported-declaration transitive axiom scan and all saved boundary controls.
That control run scanned1,068 NK declarations. A subsequent full build and
axiom scan, including the six square-chain components, passed with1,136. Both numerical theorems use
only propext, Classical.choice and Quot.sound. Six square-chain components
have separately compiled. Subsequent binary and structural checks are recorded below.

Controls reject zero widths, invalid dyadic shifts and false numerical upper
endpoints. An out-of-tree planted custom axiom was rejected by Audit.lean.
No custom axiom, native_decide or admitted proof is used in the development.

This is development validation. The final package still requires statement
comparison and exhaustive independent kernel replay (including NanoDa) on
the exact release commit. No public release or registry submission occurred.

## Subsequent completed development checks

The actual 25-state/94-transition binary geometry, all weighted growth rows,
finite-depth logarithmic certificate and binary MomentComponent now compile
and pass standard-axiom audits. The full unit conductor, exact prime-block
graph isomorphism, generic lexicographic/word capacity and prime-depth
capacity barrier also compile warning-free. Their saved controls are in audit/.
The prime-structure audits contain24 positive/negative controls and15 axiom
reports; all use only the permitted standard axioms. Binary capacity has its
actual-alphabet supermultiplicativity and limit proof.

The last aggregate build before those final additions checked2,404 NK
declarations. A new aggregate audit is still required for the enlarged import
surface. Odd215's numerical moment certificate passed; Odd437's monolithic
numerical check was stopped for memory pressure and split into smaller
kernel checks; two chunks plus their parent assembly now pass. The first
fixed-target geometry chunk also passes. A sampled monolithic geometry
process reached12.8GB and was canceled in favor of the same chunk strategy. This cancellation is not a failed mathematical check.
The complete chunked Odd215 geometry subsequently passed in168 seconds,
and its actual MomentComponent passed in15 seconds. All256 source chunks
for Odd437 and64 for Odd215 were independently checked by the generator audit
against the complete target tree. The full chunked Odd437 numerical certificate subsequently passed in188
seconds. Its generator exactly reproduces the checked source. Odd437 geometry
and unconditional square assembly remain pending. Subsequent large modules
disable asynchronous theorem elaboration to avoid overlapping kernel reductions.

The fast geometry checker has a proved refinement to the original checker.
Production residue masks and deliberately corrupted mask/prefix/tree controls
pass; no original geometry assumption was removed. Metadata passes the official
upstream v0.4 schema (PyYAML6.0.3, jsonschema4.26.0). The supplementary source
guard passes; it is not a substitute for the transitive axiom scan or replay.

The official Comparator/Lean/NanoDa installation smoke test passed. It covered
the official simple_match control only. See REPLAY_TOOLCHAIN.md; the complete
nk-lean comparison and independent replay are still pending.
