# Square assembly source review

Reviewed 2026-09-20, read-only, without any Lean build or large certificate replay. The parent reports Odd215Moments already built; Odd437Moments and SquareApplication remain pending at this review boundary.

**No blocking mathematical or assembly mismatch was found.** This is an independent source and exact-arithmetic review, not confirmation that the pending modules elaborate or that their large kernel reductions have finished.

## Odd components

| Component | Full base | Root / free multiplicity | Width denominator | Moment exponent |
| --- | ---: | ---: | ---: | --- |
| 215 | 98771297640625 = 215^6 | 9938375 = 215^3 | 99999974386028 | 26536176765267 / 10^15 |
| 437 | 6964478817623209 = 437^6 | 83453453 = 437^3 | 100000118525840 | 67878931321877 / 10^15 |

Both component definitions use the same alpha, 75806770413 / 10^11. Their literal bases are the squares of their literal roots. The retained-word lift has multiplier `(p*q)^((k-1)*e)`, which is precisely the displayed root for k=2,e=3. Thus neither numeric theorem omits or double-counts the free digits.

The intervals are copied without rescaling. The width bound follows from full-support filter membership and the actual row width bound. Each low moment identity invokes the tree's sortedness theorem, which supplies the distinct-word condition needed to turn a sum over literal rows into the support moment. This prevents duplicate rows from silently inflating the moment. Geometry and numeric proofs refer to the same named tree, denominator, and width data.

The 437 one-sided numeric checker is sound on inspection. To bound `(w/D)^f` below, it only needs a positive upper bound for the reciprocal power `(D/w)^f`; positivity of the true power and its upper enclosure imply positivity of that upper bound. Removing positivity of the computed *lower* endpoint therefore removes an unnecessary condition. The reciprocal and moment comparison directions are correct. Chunked numeric-tree equalities tie the checked tree to `odd437Tree`; I did not independently evaluate their large integer reductions.

## Nine-component assembly

The six chain components, binary component, and two odd components use the same rational alpha. Their nine f values agree exactly with `certificates/square/certificate.json`. Independent rational addition gives

    sum(f_i) - alpha = 9663 / 250000000000000 > 0.

The finite bases are pairwise coprime. The binary base is `4^(10^15)`; the assembly obtains coprimality by raising the proved coprimality of 4 with each remaining base. It does not ask `decide` to expand that enormous power. The other bases are the six prime squares, 215^6, and 437^6. The nine-component list is nonempty.

`powerLowerBound_of_intervalMoments` consumes the actual component alphabets and their moment bounds. No transfer conclusion or desired lower bound is inserted as a premise. The resulting conclusion is the all-N `PowerLowerBound`, not merely an asymptotic statement with an exponent loss.

Possible elaboration pressure remains a build concern rather than a discovered error: the two `change` steps must reduce the component projections, and the odd moment `rw`/`simpa` steps must identify the lifted base and multiplier. The matching symbolic expressions and literal integer identities support these steps, but only the parent's pending Lean build settles them.

## Mathematical exposition

The previous substantive scope fixes are present in `PROOF.md`: capacity intervals lie inside [0,1]; full width 1 is allowed for capacity; the prime-depth barrier is explicitly limited to ordinary interval capacity; it is not a global Furstenberg–Sárközy upper bound. Binary geometry is correctly described as unchanged. P0179 receives credit for the first four swaps, P0180 for the later cooperative changes. Neither global optimality nor optimality after reweighting the current support is claimed. Naslund's interval method and the classical/unit-group/Mathlib inputs are attributed.

Only minor precision/status edits remain worth considering:

1. State `k >= 1` explicitly in the opening criterion and `d >= 1` in the arbitrary-seed paragraph. These are the formal domains; the prose currently makes them implicit.
2. State `e >= 1` explicitly beside the prime-depth capacity formula if that formula is meant to quote the exact implemented theorem.
3. Lines 130–131 conservatively say both odd checks are in progress, whereas Odd215Moments has now built. Until final completion, “the remaining 437 check and final assembly” would be more current. Do not replace this with a completion claim until the final build and axiom audit pass.

These are not proof gaps. I found no remaining substantive overclaim in the reviewed mathematical account.

## Reviewed file pins

SHA-256:

```text
cb4503b11857809795312a6a1ebc80a105170e55d4358e764c3d8c93f475b7f0  NK/Certificates/SquareApplication.lean
7926ccead0b3a3f5f8015e537d6c7c4b961a5e80d5db993f1d1c282a23d1ddab  NK/Certificates/Odd215Moments.lean
0c153a66cb4b5b28328155976f60faf903fbd174626c0a2bfb7cc35c83696332  NK/Certificates/Odd437Moments.lean
a24b52b0dd10981da9226627f8f7fd38f5fdd5fe087c8587560f91bb156e84a5  NK/OneSidedPairMoment.lean
c3577dd17e99f5c262c5e690bb3b24c1748bab57c94077800f9cd49abfa57ea8  PROOF.md
```

Additional source interfaces inspected: `RetainedPairAlphabet.toIntervalAlphabet_moment`, `PairCertificateTree.toAlphabet_moment`, both odd numeric theorem conclusions, `MomentComponent`, `powerLowerBound_of_intervalMoments`, and the binary/chain component definitions. No source changes, build, full numeric replay, or publication action were performed.
