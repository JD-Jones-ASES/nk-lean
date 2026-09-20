# One-sided retained-pair moment checker audit

The only repository file authored in this increment is `NK/OneSidedPairMoment.lean`. Existing numerical dependencies, generated data, and running certificate proofs were not modified or stopped.

## Mathematical argument

For S>0, x>0, and x≤H/S, the integer upper endpoint H is necessarily positive. Outward rounding gives

`floor(S²/H)/S ≤ S/H ≤ 1/x`.

Apply this with x=(D/w)^(fn/fd) and H equal to the upper endpoint of the existing `rpowBounds`. Its soundness theorem supplies x≤H/S from the checked dyadic/logarithmic reduction hypotheses. The true real power is positive because D,w>0; D>0 follows from the retained lower reduction inequality and w>0. Taking the reciprocal gives the desired lower bound for (w/D)^(fn/fd).

Consequently no evaluation of `rpowBounds.lo>0` is needed. That old condition existed to control the *other* reciprocal endpoint, which the moment lower estimate never uses. The new checker retains the same width positivity, exponent-denominator positivity, shift inequalities, and upper-log reduction check. Positive scale remains an explicit premise of every soundness theorem.

`width_lower`, `lowerSum_sound`, and `moment_bound` all refer to the existing `PairMomentCertificate.widthBounds` / `lowerSum`. There is no numerical-endpoint change, approximation change, mathematical-statement change, or new unproved comparison. `widthValid_of_full` and `valid_of_full` explicitly transfer old validity to new validity.

## Performance diagnosis behind the change

Read-only counts found 4,913 leaves and 1,861 distinct widths for the 215 component, versus 19,683 leaves and 19,683 distinct widths for 437. Thus 437 has approximately 4.01 times the rows and 10.58 times the distinct expensive inputs. Identical-input kernel caching can therefore make the runtime ratio much larger than the row-count ratio; this is a plausible explanation, not a measured profiler result.

No giant rational-exponent evaluation was found. Width computations use fixed 40-term logarithm and 31-term exponential series, with exactly three squarings. Width shifts are 8–12 for 215 and 6–13 for 437. The original monolithic proof checks every width and separately reduces the complete lower sum. The new checker removes the lower-power endpoint calculation from the validity pass; it does not promise a particular speedup.

A robust complementary fallback is already supported by the existing named tree: 437 has 256 frontier chunks of 76 or 77 leaves. Prove local validity and exact literal lowerSum equalities for each chunk, then assemble the 255 upper branches from child theorems and literal additions. The final comparison should rewrite by the proved root sum and check only the resulting small integer inequality. Avoid a second root-wide `decide` that recomputes the original sum.

## Verification scope

The new module builds without warnings. Small exact controls are in `audit/one-sided-pair-controls.lean`: a direct reciprocal inequality, an actual width power and miniature full moment certificate, and rejection of zero width, zero exponent denominator, insufficient reduction depth, and a false target upper endpoint. A zero-scale example demonstrates why the separate positive-scale theorem premise must remain. No large certificate was launched by this agent.

Final result: the entire controls file exits successfully. The four printed soundness theorems have exactly `propext`, `Classical.choice`, and `Quot.sound`. The first scratch-control attempt needed explicit simplification of casts of 0 and 1 in two example conclusions; the final rerun is clean, and the repository module required no change. `git diff --check` is clean for the new module. No further Lean invocations are running in this lane.

Module SHA256: `a24b52b0dd10981da9226627f8f7fd38f5fdd5fe087c8587560f91bb156e84a5`.
