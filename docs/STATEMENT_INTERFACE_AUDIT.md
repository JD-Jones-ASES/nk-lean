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

Following the initial source review, both complete odd components and
`SquareApplication.lean` compiled, with the final square application
warning-free. The completed project build and transitive axiom audit cover
10,794 NK declarations and admit only the three permitted standard axioms.
The 19 intentional Challenge placeholders are the only theorem placeholders.
These build results were recorded by the main verification lane; this reviewer
did not rerun them.

A subsequent read-only check confirmed that the sole square-assembly proof
change introduces `hpower (n : ℕ) : Nat.Coprime (4 ^ n) b` from the already
proved `Nat.Coprime 4 b`, using `Nat.Coprime.pow_left`, then specializes n to
10^15. This keeps the large power symbolic. It changes no theorem statement,
component, exponent, coprimality premise, or moment-surplus calculation, and
introduces no additional assumption.

Exact Comparator comparison and NanoDa replay on the final candidate remain
separate pending gates. The saved-control audit rerun is recorded separately
by the main verification lane. This source review does not discharge these
mechanical checks. The installed-tool smoke test in `REPLAY_TOOLCHAIN.md`
covers only the official small control, not nk-lean. See `PROOF_STATUS.md` and
`VERIFICATION.md` for subsequent results.
