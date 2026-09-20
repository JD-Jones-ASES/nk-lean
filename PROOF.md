# Mathematical account

The theorem `NK.powerLowerBound_of_intervalMoments` is a general finite-data
criterion for every k≥1. For each of finitely many pairwise coprime bases b_i=s_i^k≥2,
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

For k,d≥1, define B_k(d)=∏p|d p^(k ceil(v_p(d)/k)). Mathlib's ceiling-root divisibility
adjunction gives d|z^k iff B_k(d)|z^k. Consequently copying a seed interval
to every residue of its fiber in B_k(d) never collapses a nonzero power arc.
The resulting interval alphabet has exactly B_k(d)/d copies of each seed
interval, so its cardinality and every real moment acquire that factor.
Both the actual copied alphabet and the factor identities are proved.
For example d=9,k=6 gives B=729 and81 copies; lifting instead to an
arbitrarily larger perfect power would fail zero detection.

## Which depth searches can matter

For a prime p and k≥1 the unit kth-power image stabilizes at the sufficient
conductor s_p(k)=v_p(k)+1 for odd p, at1 for p=2 and odd k, and at
v_2(k)+2 for p=2 and even k. This covers singular primes p|k as well as
ordinary Hensel lifting. These are standard unit-group facts, now proved in
the interface used here. The conductor satisfies s_p(k)≤k except at (2,2).
No minimal-conductor claim is needed.

Outside that exception, take the first unequal base-p^k digit of two
residues modulo p^(ke). A nonzero kth power in a single p^k block is a unit:
a nonunit root would already give zero in that block. Conversely the unit
conductor theorem extends the first-block kth-power condition through all
remaining digits. This proves an actual graph isomorphism with the e-fold
lexicographic power of the one-block graph, including nonunit differences
whose first unequal block occurs later.

For any finite digraph G, let M_f(G) be the supremum of interval moments
over all selected vertices and all positive intervals contained in[0,1]
and ordered by its arcs; full width1 is allowed in this capacity definition.
Actual nesting proves M_f(G∘H)≥M_f(G)M_f(H). For the reverse inequality,
take the hull of each occupied G-fiber and normalize its H-intervals inside
that hull. The hulls form a G-alphabet and each normalized fiber has moment
at most M_f(H). Therefore, for f≥0,

    M_f(G∘H)=M_f(G)M_f(H),
    M_f(G_k(p^(ke)))=M_f(G_k(p^k))^e,       e≥1, (p,k)≠(2,2).

The formal result ranges over every support and every admissible width
assignment. Thus extra depth at a single such prime cannot improve the
normalized interval capacity. This is a barrier for this interval method at
p^(ke) and f≥0, not an upper bound on the integer extremal function D_k(N).
It does not rule out coupled-prime gains.
Binary squares have conductor3 greater than block length2: five is a square
modulo4 but not modulo16. The extra bit explains why the binary depth
problem is different.

## Binary capacity and the finite witness

Let U_m(f) be the supremum of actual square-interval moments modulo4^m.
Nesting gives U_(m+n)≥U_m U_n; choosing the binary digits0 and2 gives
U_m≥2^m, and widths≤1 give U_m≤4^m. Applying the subadditive limit theorem
to −log U_m proves

    Λ(f)=lim_m U_m(f)^(1/m)=sup_(m≥1) U_m(f)^(1/m),   2≤Λ(f)≤4.

These statements are formalized for f≥0. They do not assert an attained
stationary optimizer, a Bellman identity, or a quantitative convergence rate.
The stronger factor-two/Bellman statements in the Lab research notes are
outside the present formal comparison surface.

The numerical lower witness uses Naslund's actual25-state,94-branch policy.
Its geometry, positive rational weights and all weighted row inequalities
are checked in Lean. A proved induction constructs a real interval alphabet
at every finite depth. At m=10^15 its moment is at least
2^(−f) a^(m−1)/4, with

    f=15494199041779/10^14,
    a=1430119207986461/(5·10^14).

The initialization and final shrink are charged explicitly. A logarithmic
certificate proves that this finite alphabet meets the required moment at
α=75806770413/10^11; no infinite-policy optimizer is assumed.

## Numerical applications and their scope

Square differences at exponent0.75806770413, fourth powers at0.9142 and
sixth powers at0.95295 are closed all-N Lean theorems. The square proof
assembles the actual binary, six chain and two odd components through the
general criterion. Exact geometry and numerical checks have all passed.
PROOF_STATUS.md records the remaining independent verification gates.

The square gain starts with P0179's four support replacements and width
optimization over the pinned Naslund0.75806746 witness. P0180 adds cooperative
three-vertex changes in the437=19·23 retained alphabet, further width
reoptimization, and reallocation of all nine moment exponents. The215 component and binary
transition geometry are unchanged. Ten final support positions differ from
the prior P0179 certificate. This is a small numerical improvement with a
new exact witness, not a global optimum. A fixed-geometry numerical boundary
near0.7580677041313194 explains the last digits but does not bound other
supports, reoptimized widths even on the same support, other policies or
prime couplings, or the unrestricted integer problem.

The research evidence is pinned at Analytic-Lab commit
916d0d604fa36c511b73f7aa214e49c16b637796. Naslund's interval method is a source
theorem; classical unit groups, CRT and Mathlib's ceiling-root adjunction
are prior theory. The development combines them with the general-k transfer,
canonical copying, exact capacity statements and improved applications.
Credit and source pins are in docs/ATTRIBUTION.md.
