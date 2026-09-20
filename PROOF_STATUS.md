# Proof status

All 19 statements selected in `comparator.json` are proved in Lean.
The three numerical theorems are unconditional: for every N ≥ 1, they give
a subset of {1, …, N} with the stated size and no positive perfect-power
difference. Each lower bound uses one positive constant independent of N.

| Theorem | Exponent |
|---|---:|
| `NK.Certificates.square_power_bound` | 75806770413/100000000000 |
| `NK.Certificates.fourth_power_bound` | 4571/5000 |
| `NK.Certificates.sixth_power_bound` | 19059/20000 |

## General results

The comparison also includes:

- An interval-moment transfer theorem for every positive integer k.
- Canonical perfect-power closure, its least-multiple property,
  coprimality and idempotence, and exact interval copying from seed moduli.
- Unit-power stabilization at sufficient prime-power conductors,
  including primes dividing k, with the binary-square exception explicit.
- Exact multiplication of interval capacity under lexicographic products,
  its word version, and the resulting prime-depth capacity law.
- Supermultiplicativity of binary square moments, bounds on their capacity,
  and convergence of finite-depth roots to that capacity.

[PROOF.md](PROOF.md) explains each family and its assumptions. The numerical
applications use literal finite data, proved geometry checks, rational-power
enclosures, and the full transfer theorem. Certificate values are checked
in Lean; external search and generators are not proof assumptions.

## Mechanical checks

The full build and audit passed with Lean 4.33.0. The transitive audit covers
11,314 declarations and permits only `propext`, `Classical.choice`, and
`Quot.sound`. All 25 saved control files passed.

The unchanged official Comparator accepted proof commit
`409bcef149ae96f40f69d38a17cf8bd7330dee98`: statement and definition matching,
the axiom policy, Lean kernel checking, and NanoDa replay all passed.
[VERIFICATION.md](docs/VERIFICATION.md) records the exact evidence and the
scope of subsequent presentation edits.

`NKChallenge.lean` has 19 intentional theorem placeholders and complete
mathematical definitions. `NKSolution.lean` does not import NKChallenge; its
proof dependencies contain no admissions or definition holes.

## Limits

The exponents are certified lower bounds, without a global optimality claim.
The capacity results concern interval constructions, not upper bounds for
the unrestricted integer problem. The binary results do not give a computed
capacity, optimal policy, Bellman identity, or effective convergence rate.

The accepted replay was local on macOS using the official unsandboxed
development shim. Palomar's Linux intake and editorial review are separate.
The repository is public. Its first submission failed before proof comparison
because Palomar resolved the dependency's statement module. The
[module repair](docs/MODULE_IDENTITY.md) preserves every mathematical statement.
A new intake run is required; registration is not claimed.
