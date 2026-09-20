# Fast retained-pair query audit

Scope: `NK/FastPairCertificate.lean` in `/private/tmp/nk-lean-work`.
The implementation accelerates only finite certificate evaluation. It does not change the tree data, interval geometry, or existing alphabet constructor.

## Soundness boundary

`PowerMaskValid k m mask` checks all residues `d : Fin m` against the existing definition `KthPower.IsNonzeroPowerMod k m d`. The bit at zero is therefore checked as false; arbitrary bits at indices at least `m` are irrelevant.

`FastPrefixBlocks` returns false when either list ends before a discrepancy. Otherwise it compares entries until the first unequal pair and tests exactly the difference used by `CertificatePrefixBlocks`. A successful test supplies the old first-difference witness. Equal heads merely increase that witness index by one. The theorem requires positive `m`, so the modular difference is an element of `Fin m` even before bounded-digit assumptions are supplied.

`fastQuery_sound` is structural induction on the unchanged tree. Ordered intervals return the same answer. A successful fast prefix test implies its original prefix predicate. Otherwise a leaf requires word equality and a branch requires both recursive queries. The proof does not assume that unsuccessful fast tests are complete; one-way soundness suffices.

`fastGeometryValid_sound` applies the query refinement to every literal source row. Existing `GeometryValid` plus `Valid` remain the predicates used by the existing geometric soundness and alphabet constructor. Thus the acceleration cannot turn an unverified summary, invalid row, or wrong interval ordering into an accepted alphabet.

## Exact controls

`audit/fast-pair-controls.lean` checks production masks for square residues modulo 5, 19, 23, and 43, an additional modulus-3 control, deliberately incorrect masks including a false zero bit, both orientations of a first difference, equal/short/empty prefixes, a two-row ordered tree, and a valid-row tree rejected for overlapping intervals along a square arc. All computations use ordinary kernel reduction (`decide +kernel`), not native evaluation.

No finite performance test establishes an asymptotic runtime claim. The structural reduction removes repeated root enumeration and an existential scan over possible first-difference indices from each prefix decision.

## Verified result

The module builds without warnings. The complete controls file exits successfully. All three main soundness theorems have exactly the standard printed axioms `propext`, `Classical.choice`, and `Quot.sound`. `git diff --check` is clean for the new module.

Final module SHA256: `a1835c0deae5d0e432d24ac83abc35e20454f361ee9b3f28f3bc91b59765d701`.
Controls SHA256: `8226dcfcf282e3bd56ee1e9d7adfb54480bd5d81071545910d564e34368bb3ae`.

Rerun:

```sh
lake build NK.FastPairCertificate
lake env lean audit/fast-pair-controls.lean
```
