# Statement interface review

This AI-assisted source review compares [NKChallenge.lean](../NKChallenge.lean),
[NKSolution.lean](../NKSolution.lean), [comparator.json](../comparator.json),
[formalization.yaml](../formalization.yaml), and the corresponding library
definitions and theorem interfaces. It found no blocking mathematical
fidelity or coverage issue. Source review is distinct from mechanical
comparison and independent kernel replay; accepted official results are
recorded in [VERIFICATION.md](VERIFICATION.md).

## Interface findings

The Comparator selects 19 distinct theorems, matching the 19 intentional
statement placeholders in NKChallenge. NKChallenge imports Mathlib alone and
gives ordinary, complete bodies to its definitions. NKSolution imports the
substantive NK library and square application, without importing NKChallenge.
The selected interfaces agree with their library counterparts.

- `PowerLowerBound` asserts one positive constant, independent of `N`,
  for every integer `N ≥ 1`. The transfer accepts finite interval data
  with local moment bounds and strict exponent surplus. Common width
  bounds are derived.
- Canonical closure uses the prime-valuation formula in its definition.
  Its copying theorem constructs the full fibers, with exact cardinality
  and moment multipliers for every real moment exponent.
- Unit stabilization assumes a unit input. Full modular arcs include
  nonunit power residues. The prime-depth capacity law covers every
  selected support and admissible interval assignment, for nonnegative
  moment exponent and positive depth, outside the explicit binary-square
  exception.
- Binary capacity is the supremum of actual interval-alphabet moments.
  The results prove supermultiplicativity, bounds, and a growth limit.
  They do not give a factor-two estimate, effective convergence rate,
  computed capacity, Bellman identity, or existence of an optimizer.
- The numerical conclusions use the exact rational exponents
  `0.75806770413`, `0.9142`, and `0.95295`. Their statement types
  contain no certificate assumptions. The square proof retains Naslund's
  binary geometry and uses the odd support, widths, and moment allocation
  specified by the certificate.

The chosen representation of the binary depth is proved equal to
`10^15`. It changes neither a selected statement nor any exponent,
coprimality condition, or surplus.

## Scope of assurance

The proof-bearing NKSolution closure contains no `sorry`; NKChallenge
deliberately contains the 19 theorem placeholders used for comparison.
Agent review is not human peer review, source-author endorsement, or
Palomar acceptance. The mathematical account makes no global optimality
or worldwide record claim.

The official replay record reports successful statement and definition
matching, the standard axiom policy, Lean checking, and NanoDa checking.
Its accepted proof commit and host scope are given in
[VERIFICATION.md](VERIFICATION.md). This source review does not claim to
have independently executed those checks.
