# Proof status

This is a private development project. It is not yet a completed Palomar
package. Python/C++ certificates and floating-point search are not Lean proofs.

## Compiled general theorems and building blocks

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
  rounding primitives. Finite Taylor/logarithm series now have computable natural-number endpoints and proved outward rounding; rational-power composition is in progress.
- Constructive odd-unit square criterion modulo2^n and factor-of-four descent.

- Retained-digit forward graph projection and exact fibers, including weighted sums.
- Nonsingular prime-power unit lifting.
- Exact binary-square four-branch relation and actual interval gluing with exact moment sum.
- Literal integer geometry certificates for all 18 fourth/sixth-power seed blocks.

These declarations have compiled using Lean4.33.0 and the pinned Mathlib.
The development axiom audit permits only propext, Classical.choice and
Quot.sound. The final release still needs exhaustive independent replay.

## Work in progress
- Prime-power conductor companions, retained-word CRT interval construction, and binary finite-policy iteration.
- Proved exact arithmetic/geometry checkers and unconditional numerical
  applications: square at the strongest exact Lab target (currently
  0.75806770413), fourth0.9142, sixth0.95295.
- Binary capacity, its two-sided finite-depth estimates, and the remaining
  structural companion statements selected for the final comparator.

## Release requirements

No Challenge/Solution pair yet claims the numerical bounds. The final public
Challenge must have only permitted imports and ordinary mathematical content;
all finite data and certificate proofs belong in Solution. Completion requires
matching statement comparison, a complete axiom audit, and NanoDa replay on
an exact commit. Public release and registration have not occurred.

See SUBMISSION_PLAN.md and docs/SOURCE_AND_POLICY_AUDIT.md for the complete
scope and the pinned current intake contract. Do not describe this list of
preliminary proofs as completion of the user's full formalization goal.
