# Mathematical account

The theorem `NK.powerLowerBound_of_intervalMoments` is a general finite-data
criterion. For each of finitely many pairwise coprime bases b_i=s_i^k≥2,
choose a finite support of residues and a positive interval inside[0,1] at
each residue. Every nonzero kth-power modular difference must order the
corresponding intervals from left to right. All widths are strictly below1.
If f_i≥0, each width moment Z_i(f_i)≥b_i^α, and Σf_i>α≥0, then

    ∃c>0, ∀N≥1, ∃A⊆{1,…,N}, A has no positive kth-power difference,
      |A|≥c N^α.

This statement is now proved in Lean. `MomentComponent` contains only the
finite alphabet, perfect-power base, exponent and displayed hypotheses.
It contains no lower-bound or transfer assumption. The proof also works
at k=1 when its hypotheses hold; the intended applications have k≥2.

## Why the criterion works

Finite positive widths admit common bounds0<σ≤w≤ρ<1. Compose their affine
maps along words, least significant digit outermost. In a perfect-power
base, the first differing digit of a modular kth-power difference is itself
a kth-power arc: the common prefix factors out a kth power of the root.
Thus the composed intervals order all word arcs; widths multiply.

Stop each branch the first time its width is at mostδ=ρ^K. Every branch
stops by depthK, and every terminal width exceedsσδ. Actual finite-word
extension and partition give the exact active/terminal moment recurrence.
A pigeonhole argument selects a depth1≤e_i≤K with

    b_i^(e_i α) ≤ (K+1)|E_i|δ^f_i.

Encoding the selected equal-length words preserves cardinality, interval
order and moment. Floor interval starts at resolutionσδ and reverse the
ranks to match the decreasing convention in rk-lean. Each component has
heightH=ceil(1/(σδ)). CRT combines their supports at modulus
M=∏b_i^e_i and cardinalityQ=∏|E_i|, with heighth=1+n(H−1).
Multiplication of the local estimates gives

    M^α ≤ (K+1)^n Q δ^(Σf_i).

The strict surplusΣf_i−α>0 makes the geometric decay dominate the fixed
polynomial factor and rank cost. For a sufficiently large fixedK,
(Mh)^α≤Q. The pinned RK construction repeats in the perfect-power baseM
and producesQ^t integers up to(Mh)^t avoiding kth-power differences.
Integer-log interpolation retains the full exponent with constant1/Q
for everyN≥1. The range scaleMh need not be a perfect power and is never
used as the digit base.

## Arbitrary seed moduli

Define B_k(d)=∏p|d p^(k ceil(v_p(d)/k)). Mathlib's ceiling-root divisibility
adjunction gives d|z^k iff B_k(d)|z^k. Consequently copying a seed interval
to every residue of its fiber in B_k(d) never collapses a nonzero power arc.
The resulting interval alphabet has exactly B_k(d)/d copies of each seed
interval, so its cardinality and every real moment acquire that factor.
Both the actual copied alphabet and the factor identities are proved.
For example d=9,k=6 gives B=729 and81 copies; lifting instead to an
arbitrarily larger perfect power would fail zero detection.

## Numerical applications remain separate

Lab P0180 supplies the exact square target0.75806770413; P0177 supplies
fourth0.9142 and sixth0.95295. Their external exact certificates are pinned at
Analytic-Lab `916d0d604fa36c511b73f7aa214e49c16b637796` and independently replayable.
The finite geometry, numerical evaluator, conductor reductions and binary
policy still need complete Lean proofs before these targets may be claimed
as formalized applications. The general theorem above does not fill that gap.

Naslund's interval method is a source theorem, not a novelty claim here.
The new formal theorem consolidates that method with the arbitrary-modulus
and general-k framework. Credit and exact source pins are in docs/ATTRIBUTION.md.
