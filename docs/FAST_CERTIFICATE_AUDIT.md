# Fast retained-pair query review

[FastPairCertificate.lean](../NK/FastPairCertificate.lean) accelerates finite
certificate evaluation without changing the tree data, interval geometry,
or alphabet constructor. This note records an AI-assisted soundness review
and exact controls. The accepted official replay is documented in
[VERIFICATION.md](VERIFICATION.md).

## Soundness

`PowerMaskValid k m mask` checks every residue `d : Fin m` against
`KthPower.IsNonzeroPowerMod k m d`. The zero bit must be false. Bits at
indices at least `m` are irrelevant.

`FastPrefixBlocks` returns false when a list ends before a discrepancy.
Otherwise it compares entries up to the first unequal pair and tests the
same modular difference as `CertificatePrefixBlocks`. Success supplies
the required first-difference witness; equal heads increase its index by
one. Positive `m` ensures that the modular difference defines a member
of `Fin m`, independently of bounded-digit hypotheses.

`fastQuery_sound` proceeds by induction on the tree. Interval ordering
and successful prefix tests imply the corresponding original predicates.
Otherwise a leaf requires word equality and a branch requires both recursive
queries. Only this implication is needed; completeness of unsuccessful
fast tests is not assumed.

`fastGeometryValid_sound` applies the implication to every source row.
The alphabet constructor still requires the original `GeometryValid` and
`Valid` predicates. The faster query therefore cannot bypass a row bound,
tree summary, or interval-order condition.

## Controls

[audit/fast-pair-controls.lean](../audit/fast-pair-controls.lean) checks
production square masks modulo 5, 19, 23, and 43, an additional modulus-3
example, incorrect masks including a false zero bit, both first-difference
orientations, equal and exhausted prefixes, an ordered two-row tree, and
rejection of overlapping intervals along a square arc.

The controls use `decide +kernel`, not native evaluation. The three
soundness theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

```sh
lake build NK.FastPairCertificate
lake env lean audit/fast-pair-controls.lean
```

The implementation avoids repeated root enumeration and repeated searches
for a first-difference index. No asymptotic runtime claim follows from these
finite controls.
