# After the certified endpoint

The current square exponent is 0.75806770413. It is not an optimum over
supports, widths, policies, prime couplings or integer constructions. These
priorities reflect the observed search results, not a theorem about where
future progress must occur.

## Coupled-prime supports

The concrete gains came from cooperative support changes and width optimization
in the 437 = 19·23 component. Broaden the exhausted last-digit triple moves:
use tight weighted paths to identify shared bottlenecks, then test specified
four-to-six-point changes involving middle or leading retained digits. Reweight
jointly and compare the final nine-component allocation. A local gain must pay
for every displaced component; raw moment gain alone is insufficient.

Different neighborhoods in the 215 component and new prime couplings remain
open. The prime-depth capacity theorem rules out improvement from extra depth
alone at the covered individual primes. It does not exclude coupled gains.

## Binary states and policies

Binary squares are the conductor exception. The next distinct route is an
expanded state and topology class, guided by residuals of the written four-cut
optimization. Promote useful child windows to new states instead of fitting
all children back into Naslund's 25-state library. Include required parity and
reflection variants. Previously tested unrollings, selected topology changes
and library envelopes are bounded numerical evidence, not capacity bounds.

Any accepted rational policy needs exact geometry and weighted growth checks,
initialization and finite-depth costs, and a fresh global allocation. Neither
stationary optimality nor a Bellman identity or convergence rate is assumed by
the present Lean package.

## A rigorous fixed-support optimization target

For a fixed finite directed acyclic support, positive widths w_v fit ordered
intervals in [0,1] exactly when every directed path P satisfies Σ_(v∈P) w_v≤1
(include singleton paths). Necessity follows by placing successive disjoint
intervals along a path. For sufficiency, place each interval after the longest
weighted path ending immediately before its vertex; the path constraints keep
all right endpoints at most one.

For 0<f<1, choose reference widths x_v>0 and nonnegative weights λ_P on paths,
with Σ_(P∋v) λ_P ≥ f x_v^(f−1). Concavity gives

    Σ_v w_v^f ≤ (1−f) Σ_v x_v^f + Σ_P λ_P.

Indeed, w_v^f≤(1−f)x_v^f+f x_v^(f−1)w_v; sum the tangent inequalities, use
the path-cover inequalities, then the path constraints. Outward rational power
enclosures can turn this elementary bound into an exact certificate. Large
path weights also suggest which cooperative deletions to search.

Implementing such a certificate would give a meaningful endpoint to width
optimization on one specified support. This is a proposed next development,
not part of the present checked certificates or the 19 selected Lean statements.
It would not certify optimal support, policy, prime coupling or global exponent.
