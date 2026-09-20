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

The renamed modules build successfully. The official resolver at pipeline
commit `3561d237dcc4b28482558ad28a64d767d7cc8615` reproduces the old collision
and resolves both new names correctly. Its canonical-challenge compilation
and publication functions also succeed with the new challenge. These checks
use a local process launcher and existing dependency builds on macOS; they do
not reproduce the Linux sandbox or constitute a new Palomar intake result.

The [verification history](VERIFICATION.md) retains the earlier complete
proof replay. Further repair checks are recorded here when complete. The
replacement commit requires a new Palomar submission.
