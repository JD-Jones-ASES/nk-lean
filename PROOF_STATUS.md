# Proof status

This is a private development project. It is not yet a completed Palomar
package. Python/C++ certificates and floating-point search are not Lean proofs.

## Compiled general theorems and building blocks

- **Unconditional numerical applications**: `NK.Certificates.fourth_power_bound`
  proves `PowerLowerBound 4 (4571/5000)` and `sixth_power_bound` proves
  `PowerLowerBound 6 (19059/20000)`, through literal seed geometry, proved
  rational-power enclosures, canonical closure and the full transfer theorem.
- **Full finite-family interval-moment transfer**: from ordinary finite interval
  alphabets on pairwise coprime perfect-power bases, nonnegative moment
  exponents and strict surplus, conclude the all-N bound. Uniform width
  constants are derived internally; no transfer conclusion is assumed.
- Canonical closure free-copy alphabet, with exact cardinality and moment
  factors for arbitrary positive seed moduli.
- Definitions of the ordinary all-N power-difference-free lower bound and
  ordered interval alphabets using the full modular power image.
- Geometric-scale interpolation retaining exponent equality and constant1/Q.
- Arbitrary perfect-power-base ranked transfer through the pinned RK theorem.
- Affine interval composition, product widths, first unequal interval order,
  and integer rank rounding at a common minimum width.
- Canonical perfect-power closure: zero detection for every z including0,
  least positive perfect-power multiple, idempotence and preserved coprimality.
- Abstract stopping-mass lemma and the actual finite stopping-word tree:
  exact mass recurrence, empty horizon, first-crossing width bounds and a
  terminal-layer cardinality estimate.

- Full word-interval alphabet, preserving exact cardinality and moment.
- Shared CRT product and strict-surplus budget, assembled into the theorem.
- Analytic log/exp/rpow enclosure bounds and exact natural floor/ceiling
  rounding primitives. Finite Taylor/logarithm series and rational-power composition have computable natural-number endpoints and proved outward rounding.
- Constructive odd-unit square criterion modulo2^n and factor-of-four descent.

- Retained-digit forward graph projection and exact fibers, including weighted sums.
- Nonsingular prime-power unit lifting.
- Exact binary-square four-branch relation and actual interval gluing with exact moment sum.
- Literal integer geometry certificates for all 18 fourth/sixth-power seed blocks.

These declarations have compiled using Lean4.33.0 and the pinned Mathlib.
The development axiom audit permits only propext, Classical.choice and
Quot.sound. The final release still needs exhaustive independent replay.

## Compiled structural and binary companions

- Full unit-power stabilization at conductor v_p(k)+1 for odd primes, 1 for
  binary odd powers, and v_2(k)+2 for binary even powers. The conductor fits
  inside one k-digit block exactly outside (p,k)=(2,2); a literal square
  counterexample proves the extra binary lookahead is real.
- Exact interval-moment multiplicativity for finite directed lexicographic
  products, including empty vertex types and loops, for every f≥0.
- Actual binary finite-policy iteration, all 25 states and 94 transition
  branches, all weighted row inequalities, and the depth-10^15 component.
- Exact prime-block graph factorization and unrestricted prime-local
  moment capacity at all positive depths, outside the binary-square exception.
- Intrinsic binary capacity: supermultiplicativity of finite-depth moments,
  bounds 2≤Λ(f)≤4, and convergence of U_m(f)^(1/m) to their supremum for f≥0.
  No factor-two finite-horizon estimate or Bellman identity is claimed yet.
- Retained-word CRT construction, exact fibers, and a sound tree certificate
  checker for the two large odd alphabets.

## Compiled square application

`NK.Certificates.square_power_bound` proves the unconditional all-N square
bound at75806770413/100000000000. All nine actual components are complete.
The final serial Odd215 geometry/component replay took173/4.9 seconds;
Odd437 numerical moments took188 seconds, geometry927 seconds, and its
component6.4 seconds. SquareApplication compiled warning-free in4 seconds.
The binary modulus remains symbolic throughout.


## Release requirements

The draft Challenge/Solution pair selects19 statements, including all three
proved numerical targets. Challenge imports only
Mathlib and contains complete ordinary mathematical definitions;
all finite data and certificate proofs belong in Solution. Completion requires
matching statement comparison and NanoDa replay on an exact commit. The
complete project build and transitive audit of10,794 NK declarations pass. Public release and registration have not occurred.

See SUBMISSION_PLAN.md and docs/SOURCE_AND_POLICY_AUDIT.md for the complete
scope and the pinned current intake contract. Do not describe this list of
preliminary proofs as completion of the user's full formalization goal.
