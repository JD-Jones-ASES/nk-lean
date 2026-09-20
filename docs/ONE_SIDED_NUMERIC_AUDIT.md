# One-sided retained-pair moment checker audit

The initial checker increment authored only `NK/OneSidedPairMoment.lean`. Its mathematical argument and small-module verification are recorded below. A later production update applies the same checker and chunked proof representation to both retained-pair components; its Python-only audit is distinguished from full verifier acceptance.

## Mathematical argument

For S>0, x>0, and x≤H/S, the integer upper endpoint H is necessarily positive. Outward rounding gives

`floor(S²/H)/S ≤ S/H ≤ 1/x`.

Apply this with x=(D/w)^(fn/fd) and H equal to the upper endpoint of the existing `rpowBounds`. Its soundness theorem supplies x≤H/S from the checked dyadic/logarithmic reduction hypotheses. The true real power is positive because D,w>0; D>0 follows from the retained lower reduction inequality and w>0. Taking the reciprocal gives the desired lower bound for (w/D)^(fn/fd).

Consequently no evaluation of `rpowBounds.lo>0` is needed. That old condition existed to control the *other* reciprocal endpoint, which the moment lower estimate never uses. The new checker retains the same width positivity, exponent-denominator positivity, shift inequalities, and upper-log reduction check. Positive scale remains an explicit premise of every soundness theorem.

`width_lower`, `lowerSum_sound`, and `moment_bound` all refer to the existing `PairMomentCertificate.widthBounds` / `lowerSum`. There is no numerical-endpoint change, approximation change, mathematical-statement change, or new unproved comparison. `widthValid_of_full` and `valid_of_full` explicitly transfer old validity to new validity.

## Performance diagnosis behind the change

Read-only counts found 4,913 leaves and 1,861 distinct widths for the 215 component, versus 19,683 leaves and 19,683 distinct widths for 437. Thus 437 has approximately 4.01 times the rows and 10.58 times the distinct expensive inputs. Identical-input kernel caching can therefore make the runtime ratio much larger than the row-count ratio; this is a plausible explanation, not a measured profiler result.

No giant rational-exponent evaluation was found. Width computations use fixed 40-term logarithm and 31-term exponential series, with exactly three squarings. Width shifts are 8–12 for 215 and 6–13 for 437. The original monolithic proof checks every width and separately reduces the complete lower sum. The new checker removes the lower-power endpoint calculation from the validity pass; it does not promise a particular speedup.

Both production numerical wrappers now use the existing named-tree chunks. Odd215 has 64 frontier chunks and 63 assembled parents; Odd437 has 256 frontier chunks and 255 assembled parents. Every frontier contains 76 or 77 leaves. Local validity and exact literal `lowerSum` equalities are checked separately. Generic congruence lemmas combine child theorems and literal additions; the final comparison transports the proved root sum into a literal natural-number inequality. There is no root-wide `decide` that recomputes the complete sum.

## Verification scope

The new module builds without warnings. Small exact controls are in `audit/one-sided-pair-controls.lean`: a direct reciprocal inequality, an actual width power and miniature full moment certificate, and rejection of zero width, zero exponent denominator, insufficient reduction depth, and a false target upper endpoint. A zero-scale example demonstrates why the separate positive-scale theorem premise must remain. No large certificate was launched by this agent.

Final result: the entire controls file exits successfully. The four printed soundness theorems have exactly `propext`, `Classical.choice`, and `Quot.sound`. The first scratch-control attempt needed explicit simplification of casts of 0 and 1 in two example conclusions; the final rerun is clean, and the repository module required no change. `git diff --check` is clean for the new module. No further Lean invocations are running in this lane.

Module SHA256: `a24b52b0dd10981da9226627f8f7fd38f5fdd5fe087c8587560f91bb156e84a5`.

## Production Odd215 representation update

Odd215 previously used a monolithic `PairMomentCertificate.moment_bound` proof. It now uses the same `OneSidedPairMoment` checker and bounded numerical proof assembly as Odd437, with serial elaboration. The literal geometry, widths, scale, fixed three-squaring endpoint, exponent allocation and public `odd215_moment` statement are unchanged. The exact public statement was compared with frozen commit `99de2ade1fe572407d0295481b36f07167fa9e2e`.

Normal and optimized Python reproduce both production Numeric files byte-for-byte. Three mutations per component—an imported literal width, a flat-file width and the root alias—are rejected in both modes before output creation. An intercepted main-generation run confirms chunked numeric generation for both 215 and 437, unchanged application wrappers, and no temporary monolithic Numeric write.

| Component | Exact integer lower sum | Local comparison surplus |
|---|---:|---:|
| Odd215 | 4088483319740695586635924782 | 56253318137051129930389 |
| Odd437 | 12261338816591850911384777125 | 1424402168362429321833002 |

These surpluses are the local scaled natural comparisons, not the global exponent surplus. `NUMERIC_GENERATOR_AUDIT.json` records parameters and hashes; `CERTIFICATE_REPLAY.md` gives portable commands. This update ran no Lean builds or exports. It does not establish completion of the post-change aggregate build, Comparator or NanoDa replay, and does not claim that the representation change resolves NanoDa's resource behavior.
