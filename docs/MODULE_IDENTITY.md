# Submission module names

The first submission, at commit
`0a2e7b8cb640ab3528fef6d0e44798940c4006fd`, failed in
[Palomar run 35539225340](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/35539225340).
The retained [report excerpt](replay/module-collision-35539225340.json)
identifies the cause.

Both this project and its pinned dependency defined modules named `Challenge`
and `Solution`. Palomar searches Lake's ordered source roots before compiling
an independent copy of the challenge. Dependency roots came first, so it
selected `.lake/packages/rkLean/Challenge.lean`. That file does not declare
`NK.powerLowerBound_of_intervalMoments`. The exporter panicked while looking
up that name and exited with status 134. No solution proof check was reached.

The submission modules are now [NKChallenge.lean](../NKChallenge.lean) and
[NKSolution.lean](../NKSolution.lean). The Lake targets and comparator
configuration use those names. The 19 theorem names, definitions, proof
sources, certificates, dependency pins, permitted axioms, and NanoDa setting
are unchanged. No mathematical claim has been weakened.

The ordinary build did not expose the source-resolution collision. The audit
now runs [a module-source check](../scripts/check_module_resolution.py) under
`lake env` and requires both configured modules to resolve to this repository.
This uses the same first-match rule as Palomar. A regression check with the
old names confirms that the dependency collision is rejected.

## Verification

The renamed modules build successfully, and the full audit passes: the
source guard, module check, axiom audit, and all 25 saved Lean controls.
The [audit record](replay/module-repair-audit.json) and
[log](replay/module-repair-audit.log) retain the result. The
[source comparison and input hashes](replay/module-repair-inputs.json)
confirm unchanged code in all 96 Lean files, after accounting for the two
renames and comment changes.

The official resolver at pipeline
commit `3561d237dcc4b28482558ad28a64d767d7cc8615` reproduces the old collision
and resolves both new names correctly. Its canonical-challenge compilation
and publication functions also succeed with the new challenge. These checks
use a local process launcher and existing dependency builds on macOS; they do
not reproduce the Linux sandbox or constitute a new Palomar intake result.
The [canonical compilation record](replay/module-repair-canonical.json)
also records a passing control with the new names and failing controls
with each old name.

The rebuilt `NKSolution` export is byte-for-byte identical to the accepted
proof export: 232,434,222 bytes, SHA256
`e12be5029a582cad015d4e0e4fef200e0b31fdcd1b0c16651f710233a544cc71`.
The [export check](replay/module-repair-export.json) records the exact
targets and tool revision. This establishes identity of the exported proof
payload; it does not by itself repeat the kernel checks.

The [manual preflight workflow](../.github/workflows/palomar-preflight.yml)
calls Palomar's exact pinned Linux verification job in this repository. It
checks the selected commit without creating a registry submission. The
workflow runs only when manually dispatched.

The [official Linux preflight](https://github.com/JD-Jones-ASES/nk-lean/actions/runs/35540659599)
passed at `f324e33d76e5e578cd69c1d7909c0216df37517f`. Its
[mechanical report](replay/linux-preflight-f324e33.json) confirms the correct
source paths, high challenge trust, and acceptance by both NanoDa and the
Lean kernel. All 19 comparisons passed, with no warnings or errors.

The following documentation and evidence commit preserves all 121 inputs
in the repair manifest and the accepted metadata. The
[verification history](VERIFICATION.md) distinguishes this Linux result
from the earlier local replay. A new Palomar submission is still required.
