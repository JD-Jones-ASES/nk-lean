# Further questions

The proved exponents are lower bounds. Several ways to improve them remain
open within the interval method.

## Coupled primes

The prime-depth law covers one prime at a time. It does not determine the
best interval alphabet for a modulus with several prime factors. Changing
such supports and their widths may yield a better global moment allocation.
Any comparison must account for every component replaced by the new block.

## Binary squares

Binary squares are the exception to the prime-depth law. Their power
residues require an additional binary digit. The capacity limit exists, but
its value and optimal transition rules are unknown. A larger collection of
states could improve the finite policy used in the square construction.

## Exact bounds for fixed supports

For a finite directed acyclic graph, positive widths w_v can be placed as
ordered intervals in [0,1] exactly when every directed path P satisfies
Σ_(v∈P) w_v ≤ 1, including singleton paths. To see sufficiency, place each
interval after the longest weighted path ending before its vertex.

For 0 < f < 1, choose positive reference widths x_v and nonnegative path
weights λ_P with Σ_(P∋v) λ_P ≥ f x_v^(f−1). Concavity gives

    Σ_v w_v^f ≤ (1−f) Σ_v x_v^f + Σ_P λ_P.

This follows by summing the tangent inequalities for w_v^f and then applying
the path constraints. Rational enclosures could turn this upper bound into
an exact optimization certificate for a specified support.

These questions are outside the 19 statements selected for comparison.
A bound for one support would not establish an optimal support, transition
policy, or exponent for the unrestricted integer problem.
