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

## Verification boundary

At this review, the complete chunked Odd215 geometry and moment component and
the chunked Odd437 numerical certificate had compiled. Odd437 geometry was
running. `SquareApplication.lean` had **not yet compiled**. The source-level
square statement and proposed assembly therefore remain conditional on those
development checks completing.

The final aggregate build, transitive axiom audit, exact Comparator comparison,
and NanoDa replay on the final candidate remain separate gates. This audit
does not discharge them. The installed-tool smoke test described in
`REPLAY_TOOLCHAIN.md` covers only the official small control, not nk-lean.
See `PROOF_STATUS.md` and `VERIFICATION.md` for subsequent results; their later
dated evidence may supersede this review-time status.
