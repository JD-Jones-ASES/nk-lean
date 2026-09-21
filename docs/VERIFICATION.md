# Verification

The [official Linux mechanical preflight](https://github.com/JD-Jones-ASES/nk-lean/actions/runs/35540659599)
accepted commit `f324e33d76e5e578cd69c1d7909c0216df37517f` on
20 September 2026. It ran Palomar's unchanged reusable verification workflow,
pinned to `3561d237dcc4b28482558ad28a64d767d7cc8615`, with the standard Linux
execution profile and sandbox.

All 19 statements passed comparison, the permitted-axiom check, NanoDa,
and the Lean kernel. The [mechanical report](replay/linux-preflight-f324e33.json)
records `status: pass`, `stage: complete`, no warnings or errors, and high
trust for the Mathlib-only challenge. It confirms that both configured
modules resolved to this repository. The Comparator phase, including the
solution build, took 5,364.43 seconds.

The [module repair](MODULE_IDENTITY.md) explains the original failure and
its regression checks. The [input manifest](replay/module-repair-inputs.json)
records 121 source, build, generator, certificate, audit, and workflow inputs
at the accepted commit. The following documentation and evidence commit
preserves every recorded input and the unchanged `formalization.yaml`.
It adds the verification record; no second full replay is claimed for those
documentation changes. This successful preflight is not registry submission
or editorial acceptance.

## Earlier local replay

The complete official Comparator run accepted proof commit
`409bcef149ae96f40f69d38a17cf8bd7330dee98` on 20 September 2026.
All 19 statements passed definition and statement comparison, the permitted
axiom check, Lean kernel checking, and NanoDa replay. The run exited zero
with the final message “Your solution is okay!” after 2,777.40 seconds.

This was a local macOS run with the unchanged official tools and their
unsandboxed development shim. It is distinct from Palomar's Linux intake
and editorial review. The first public submission later failed because of
module resolution; the repair and successful Linux preflight are recorded above.

## Retained evidence

- [Full Comparator log](replay/comparator-409bcef.log).
- [Run metadata](replay/comparator-409bcef.json).
- [Accepted source and certificate hashes](replay/proof-inputs-409bcef.json).
- [Solution export metadata](replay/solution-export-409bcef.json).
- [Full build and audit log](replay/development-audit-409bcef.log).
- [Tool versions and replay instructions](REPLAY_TOOLCHAIN.md).

The accepted log has SHA256
`55b8007b6deb5185cf708e4cdf5998decb61700cf9f4e87c7bfd7a591a5f0a23`.
The Solution export has 232,434,222 bytes and SHA256
`e12be5029a582cad015d4e0e4fef200e0b31fdcd1b0c16651f710233a544cc71`.
The raw records preserve the actual commands and host paths used in that run.

## Proof checks

The full build compiles NK, NKChallenge, NKSolution, and Audit with Lean 4.33.0
and pinned dependencies. The transitive audit covers 11,314 declarations;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. All 25
saved control files pass. They cover the transfer theorem, arithmetic and
rounding, interval geometry, tree queries, binary policies, graph products,
and invalid certificate inputs.

`NKChallenge.lean` imports Mathlib alone, has complete definitions, and contains
19 intentional theorem placeholders. NKSolution does not import NKChallenge;
its proof dependencies contain no admissions. The single comparison selects
all 19 statements, leaves `definition_names` empty, and enables NanoDa.
The source guard checks 70 proof files as a supplementary check.

Finite data are checked by proved Lean verifiers. External generators merely
supply literals. The [certificate replay instructions](CERTIFICATE_REPLAY.md)
explain their deterministic output and corruption controls. The large odd
certificates divide source rows into chunks while retaining the full target
tree, so cross-chunk arcs are checked.

## Presentation edits for submission

The submission documents now state the results directly and cite public
sources. Lean edits are comments only; certificate edits change descriptive
metadata only. The [edit audit](replay/submission-edit-audit.json) checks every
Lean file against the accepted source with comments removed, checks every
certificate value, and confirms unchanged build pins and comparison settings.
Generator changes affect documentation and emitted comments only.
The [presentation input manifest](replay/submission-inputs.json) records all 118
source, build, generator, and certificate inputs after those edits.

The accepted source manifest above remains a historical record. Some file
hashes change when their comments or descriptions change. The accepted full
Comparator run is attributed to its actual commit, not to a later edited
commit.

The edited source at `3ad62e0a7147f3f5587ccb66342566559034cddb` was rebuilt
successfully. The complete audit, including all 25 saved control files,
passed again: [audit log](replay/submission-audit.log) and
[run metadata](replay/submission-audit.json).
Its freshly compiled Solution export is byte-for-byte identical to the
232,434,222-byte accepted export above, using the same targets and tools.
The [export record](replay/submission-export.json) and
[identity check](replay/submission-export-identity.json) retain the evidence.
No second full Comparator or NanoDa run is claimed for that presentation edit.
Commit `0a2e7b8cb640ab3528fef6d0e44798940c4006fd` changes only documentation
and verification records from that source; all 118 inputs in the presentation
manifest match that submitted commit. The subsequent module repair changes
file names, Lake targets, and the two configured module names; its checks are
recorded separately in [MODULE_IDENTITY.md](MODULE_IDENTITY.md).

The metadata validates against the official v0.4 schema. The title and
abstract describe the compared result families; the mathematical account
explains every selected theorem. AI assistance and agent review are disclosed
separately from human peer review and source-author endorsement.

## Binary depth representation

The finite binary certificate uses depth 10^15. To avoid expanding the
natural number 4^(10^15) during independent replay, the proof uses a chosen
depth and proves it equal to that exact value. All powers retain the chosen
depth symbolically. No theorem, numerical endpoint, or axiom is changed.
[The diagnostic note](NANODA_POWER_REDUCTION.md) records the earlier failed
replay and the correction accepted by the unchanged official checker.

## Palomar submission and the source record

The submission of `943c83f3bab7156b69c4a6235c78724fea409ab4` passed Palomar's
mechanical verification on 21 September 2026
([run 35545688971](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35545688971):
all 19 statements, the axiom policy, Lean kernel checking, and NanoDa), and
its automated review identified no blocking problem. The review noted that
`formalization.yaml` omitted references named in [ATTRIBUTION.md](ATTRIBUTION.md).
The following commit adds four `background` sources, the unit-group note behind
the conductors and three unit Cayley graph papers as graph-literature context,
and corrects one title in the attribution. It changes no Lean, certificate,
build, or comparator input: all 121 inputs in the
[repair manifest](replay/module-repair-inputs.json) hash unchanged. Registration
requires a new submission at that commit; none is claimed.
