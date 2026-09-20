# One-sided moment checker review

[OneSidedPairMoment.lean](../NK/OneSidedPairMoment.lean) proves a lower bound
for an interval moment using only the reciprocal power's upper endpoint.
This note records an AI-assisted mathematical review, exact controls, and
the finite numerical assembly. The accepted official replay is recorded
separately in [VERIFICATION.md](VERIFICATION.md).

## Reciprocal inequality

If `S > 0`, `x > 0`, and `x ≤ H/S`, then `H > 0` and

```text
floor(S²/H)/S ≤ S/H ≤ 1/x.
```

For a width `w/D`, take `x = (D/w)^(fn/fd)` and let `H` be the
integer upper endpoint of `rpowBounds`. Its soundness theorem supplies the
upper estimate from the checked dyadic and logarithmic reduction conditions.
The true power is positive because `D,w > 0`; denominator positivity also
follows from the retained lower reduction inequality and width positivity.
Taking reciprocals gives the required lower bound for `(w/D)^(fn/fd)`.

No positive computed lower endpoint is needed. The checker retains width
positivity, exponent-denominator positivity, the shift inequalities, the
upper logarithmic reduction check, and the positive-scale premise.

`width_lower`, `lowerSum_sound`, and `moment_bound` use
`PairMomentCertificate.widthBounds` and `lowerSum`, preserving their
exact numerical endpoints. The lemmas `widthValid_of_full` and
`valid_of_full` show that the full checker hypotheses imply the one-sided
hypotheses.

## Finite numerical assembly

The 215 component has 4,913 rows and 1,861 distinct widths. The 437 component
has 19,683 rows, all with distinct widths. Width calculations use 40 logarithm
terms, 31 exponential terms, and three squarings. The dyadic shifts range
from 8 to 12 for 215 and from 6 to 13 for 437.

The numerical proofs use 64 frontier chunks for 215 and 256 for 437, each
containing 76 or 77 leaves. Local validity and exact `lowerSum` equalities
are checked separately. Generic congruence lemmas combine the child proofs
with literal additions. The root comparison uses the proved sum rather
than recomputing the entire sum by a root-level `decide`.

| Component | Exact integer lower sum | Local comparison surplus |
| --- | ---: | ---: |
| Odd215 | 4088483319740695586635924782 | 56253318137051129930389 |
| Odd437 | 12261338816591850911384777125 | 1424402168362429321833002 |

These are local scaled natural-number comparisons, not the global surplus
`sum(f_i) − alpha`. The proof representation leaves the geometry, widths,
scale, exponents, and public moment statements unchanged.

## Controls and regeneration

[audit/one-sided-pair-controls.lean](../audit/one-sided-pair-controls.lean)
checks the reciprocal inequality, a width power, and a small full moment
certificate. Negative controls reject zero width, a zero exponent denominator,
insufficient reduction depth, and a false target upper endpoint. A zero-scale
example tests the need for the positive-scale premise. The four soundness
axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

```sh
lake build NK.OneSidedPairMoment
lake env lean audit/one-sided-pair-controls.lean
```

The Python generator checks reproduce both numerical files in normal and
optimized modes. For each component, mutations to an imported width, a
flat-file width, and the root alias are rejected before output creation.
An intercepted main-generation test checks that numerical output is chunked
and application wrappers are preserved. These generator tests do not replace
Lean checking of the literal comparisons. Portable regeneration commands are
in [CERTIFICATE_REPLAY.md](CERTIFICATE_REPLAY.md).
