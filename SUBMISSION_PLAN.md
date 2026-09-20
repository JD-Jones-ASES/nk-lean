# Palomar submission

## Entry title

Lower bounds for sets without perfect-power differences

## Abstract

Let D_k(N) be the largest size of a subset of {1, …, N} with no positive
k-th-power difference. We prove D_k(N) ≥ c_k N^α_k for every N ≥ 1, with
positive constants c_k and exponents 0.75806770413, 0.9142, and 0.95295 for
squares, fourth powers, and sixth powers. The proofs use a general
interval-moment criterion for every positive integer k. We also prove
arithmetic lifting results, exact product and prime-depth laws for interval
capacity, and existence of the binary square capacity limit. The square
construction refines Naslund's published example while retaining its binary
transition rules. All selected statements are proved in Lean.

## Submission files

Use this public repository at the exact 40-character replacement commit on
`main`. `formalization.yaml` contains the entry metadata. The single
`comparator.json` selects 19 theorems in `NKChallenge.lean`; `NKSolution.lean`
imports their proofs. The Lean toolchain, Lake manifest, and MIT license
are committed.

The [mathematical account](PROOF.md) explains the full selected scope.
[Attribution](docs/ATTRIBUTION.md) records the public mathematical and formal
sources. [DISCLOSURE.md](DISCLOSURE.md) describes AI assistance and review.
[Verification](docs/VERIFICATION.md) retains the successful local replay
and distinguishes it from official intake.

## Remaining release steps

1. Confirm the exact replacement main commit and its verification record.
2. Submit the public repository, that full commit hash, and `comparator.json`
   through the current Palomar intake. Its Linux mechanical checks and
   editorial review are distinct from the completed local verification.
3. Record the resulting entry and version only after registration is confirmed.

The submission of `0a2e7b8cb640ab3528fef6d0e44798940c4006fd` failed during
mechanical verification. The [repair record](docs/MODULE_IDENTITY.md) explains
the module-name collision and the replacement checks. A new submission is
required; no registration is claimed. The [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
sets the package and metadata requirements.
