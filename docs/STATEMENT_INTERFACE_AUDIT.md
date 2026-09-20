# Statement interface audit

Independent source review, 20 September 2026. This review read `Challenge.lean`,
`Solution.lean`, `comparator.json`, `formalization.yaml`, and the corresponding
library definitions and theorem interfaces. It made no proof-source changes,
ran no Lean builds, and does not claim successful mechanical comparison or
independent kernel replay.

## Findings

No blocking mathematical fidelity or coverage issue was found. The comparator
selects exactly 19 distinct theorems, matching the 19 intentional theorem
placeholders in Challenge. Challenge imports Mathlib alone and gives complete,
ordinary bodies to its definitions. Solution imports the substantive NK library
and square application; it does not import Challenge. The selected theorem
interfaces and mathematical definitions agree with their source counterparts.

- `PowerLowerBound` asserts one positive constant, independent of N, for every
  integer N at least one. The transfer accepts finite interval data with local
  moment bounds and strict exponent surplus; common width bounds are derived.
- Canonical closure uses the displayed prime-valuation formula. Its copying
  theorem gives the actual full-fiber support, exact cardinality multiplier,
  and exact moment multiplier for every real f.
- Unit stabilization explicitly assumes a unit input. Full modular arcs use
  all power residues, including nonunits. The prime-depth capacity law covers
  every support and admissible interval assignment, for f at least zero and
  positive depth, with the binary-square exception stated explicitly.
- Binary capacity is the supremum of actual interval-alphabet moments. The
  selected results assert supermultiplicativity, bounds, and a growth limit.
  They do not assert a factor-two estimate, effective convergence rate,
  computed capacity, Bellman identity, or optimizer existence.
- The numerical conclusions have the exact rational exponents
  0.75806770413, 0.9142, and 0.95295. Their statement types contain no certificate
  assumptions. The square proof retains the published binary geometry and
  uses the revised odd support, widths, and allocation described in metadata.

The metadata distinguishes agent review from human peer review, source-author
endorsement, and Palomar acceptance. It makes no global optimality or worldwide
record claim. Its zero-sorry count concerns the proof-bearing Solution closure;
Challenge deliberately contains the 19 statement placeholders.

## Verification boundary and later evidence

At the earlier snapshot following this source review, both odd components
and SquareApplication compiled, and the transitive audit covered 10,794 NK
declarations. Those results came from the main verification lane; this reviewer
did not rerun them. The final candidate's audit covers 11,314 declarations.

The earlier generic coprimality helper was specialized to the literal depth
10^15. It preserved the mathematical statement but did not prevent NanoDa's
eager natural-power reduction. The final candidate instead uses the proved
chosen depth described in NANODA_POWER_REDUCTION.md. Its exact value remains
10^15; no selected statement, exponent, coprimality premise or surplus changes.

The main verification lane subsequently completed the unchanged official
Comparator replay on proof commit
409bcef149ae96f40f69d38a17cf8bd7330dee98. Statement/definition matching, the axiom
policy, Lean replay and NanoDa all passed. See VERIFICATION.md for its retained
evidence and macOS host scope. This historical source review is not presented
as independently executing those mechanical checks.
