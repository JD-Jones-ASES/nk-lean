# Mathematical account

For positive integers k and N, let D_k(N) be the largest size of a subset of
{1, …, N} containing no two elements whose positive difference is a kth power.
The numerical theorems give constants c_k > 0, independent of N, such that

    D_2(N) ≥ c_2 N^0.75806770413,
    D_4(N) ≥ c_4 N^0.9142,
    D_6(N) ≥ c_6 N^0.95295

for every N ≥ 1. The proofs use a general interval-moment criterion, exact
finite certificates, and structural results about prime-power moduli.

## The interval-moment criterion

An interval alphabet modulo b consists of a finite set A of residues and an
interval I_x = [a_x, a_x + w_x] inside [0, 1] for each x in A, with w_x > 0.
Whenever y − x is a nonzero kth power modulo b, the intervals satisfy
a_x + w_x ≤ a_y. Its moment at a real exponent f is

    Z_A(f) = Σ_(x ∈ A) w_x^f.

The theorem NK.powerLowerBound_of_intervalMoments applies for every k ≥ 1.
Take a nonempty finite family of such alphabets on pairwise coprime bases
b_i = s_i^k ≥ 2. Suppose all widths are less than one, f_i ≥ 0, α ≥ 0, and

    Z_i(f_i) ≥ b_i^α for every i,       Σ_i f_i > α.

Then D_k(N) ≥ c N^α for a fixed c > 0 and every N ≥ 1. The hypotheses contain
only finite alphabets and their moment inequalities. The lower bound is
derived from these data.

Finite positive widths admit common bounds 0 < σ ≤ w ≤ ρ < 1. Compose the
affine interval maps along words, with the least significant digit outermost.
In a perfect-power base, the first differing digit of a modular kth-power
difference is itself a kth-power arc: the common prefix factors out a kth
power of the root. The composed intervals therefore order every word arc,
and their widths multiply.

Stop each branch when its width first becomes at most δ = ρ^K. Every branch
stops by depth K, and each terminal width is greater than σδ. An exact
recurrence for the moments of active and terminal words, followed by a
pigeonhole argument, selects a depth 1 ≤ e_i ≤ K with

    b_i^(e_i α) ≤ (K + 1) |E_i| δ^f_i.

Encoding these equal-length words preserves their number and interval order.
Round their interval starts down at resolution σδ, and reverse the ranks to
use a decreasing rank on each directed arc. Each component has height
H = ceil(1/(σδ)). The Chinese remainder theorem combines the supports into a
ranked block with modulus M = ∏_i b_i^e_i, size Q = ∏_i |E_i|, and height
h = 1 + n(H − 1), where n is the number of components. Thus

    M^α ≤ (K + 1)^n Q δ^(Σ_i f_i).

The positive surplus Σ_i f_i − α makes geometric decay dominate the
polynomial and rank costs. For a sufficiently large fixed K, this gives
(Mh)^α ≤ Q. The ranked construction repeats in the perfect-power base M
and produces Q^t integers in {1, …, (Mh)^t} with no positive kth-power
difference. Interpolation between these scales gives the constant 1/Q
for every N ≥ 1. The range scale Mh need not be a perfect power; the digit
base is M.

## Canonical lifting of seed moduli

For k, d ≥ 1, define

    B_k(d) = ∏_(p | d) p^(k ceil(v_p(d)/k)).

This is the least positive perfect kth power divisible by d. For every
natural number z, including zero,

    d divides z^k  if and only if  B_k(d) divides z^k.

For positive d and e, the closure preserves coprimality: B_k(d) and B_k(e)
are coprime exactly when d and e are coprime. It is also idempotent:
B_k(B_k(d)) = B_k(d). These facts allow arbitrary positive seed moduli to
be replaced by compatible perfect-power bases. The arithmetic uses
Mathlib's ceiling-root divisibility theorem.

Copy each seed interval to every residue in its reduction fiber modulo d.
The divisibility equivalence ensures that a nonzero power arc cannot
collapse to a zero difference in the seed. The resulting interval alphabet
has exactly B_k(d)/d copies of each interval. Its cardinality and every real
moment acquire this same factor, while its widths are unchanged.

For example, d = 9 and k = 6 give B_k(d) = 729 and 81 copies per seed
interval. An arbitrary larger perfect-power multiple would not necessarily
preserve the required zero-difference criterion.

## Unit conductors and prime-power graphs

For a prime p and k ≥ 1, a sufficient conductor for kth powers of units is

    s_p(k) = v_p(k) + 1             if p is odd,
    s_2(k) = 1                     if k is odd,
    s_2(k) = v_2(k) + 2             if k is even.

If p does not divide u and n ≥ s_p(k), then u is a kth power modulo p^n
exactly when it is a kth power modulo p^s_p(k). This includes primes
dividing k as well as the nonsingular lifting case. These conductor formulas
come from classical unit-group arithmetic; no minimal-conductor claim is
required.

The inequality s_p(k) ≤ k holds exactly outside (p, k) = (2, 2).
Consequently, outside that exception, a unit is a kth power modulo p^n
for n ≥ k exactly when it is one modulo p^k.

Let G_k(m) be the directed graph on residues modulo m, with an arc x → y
when y − x is a nonzero kth power modulo m. For e ≥ 1 and (p, k) ≠ (2, 2),
write residues modulo p^(ke) in base p^k, starting with the least significant
block. A nonzero kth power in one block is a unit, since a nonunit root
would already give zero modulo p^k. The unit conductor theorem extends a
power condition in the first unequal block through the remaining blocks.
This gives an exact graph isomorphism between G_k(p^(ke)) and the e-fold
lexicographic power of G_k(p^k), including differences whose first unequal
block occurs later.

## Interval capacity

For a finite directed graph G and f ≥ 0, let M_f(G) be the supremum of
interval moments over all selected vertices and positive intervals inside
[0, 1] ordered by the graph's arcs. Width one is allowed in this capacity
definition, and the empty selection is allowed.

Nesting interval alphabets proves M_f(G ∘ H) ≥ M_f(G) M_f(H). For the reverse
inequality, take the hull of the intervals in each occupied G-fiber and
normalize the H-intervals inside that hull. The hulls form a G-alphabet,
and each normalized fiber has moment at most M_f(H). Therefore

    M_f(G ∘ H) = M_f(G) M_f(H).

For words of length e, put an arc from v to w when some position j has
equal entries at all earlier positions and a G-arc from v_j to w_j. For
graphs without loops, this is the first-difference rule. Iterating the
identity gives capacity M_f(G)^e for every e ≥ 0, including the single
empty word at e = 0.

Combining this with the prime-power graph isomorphism gives

    M_f(G_k(p^(ke))) = M_f(G_k(p^k))^e

for p prime, k, e ≥ 1, f ≥ 0, and (p, k) ≠ (2, 2). In particular, every
individual interval alphabet at modulus p^(ke) has moment at most the
right-hand side. The statement covers every support and admissible choice
of widths.

Extra depth at a single such prime cannot improve its normalized interval
capacity. This is a restriction on the interval method, not an upper bound
on D_k(N). Coupled-prime constructions remain possible.

Binary squares have conductor 3, greater than block length 2: five is a
square modulo 4 but not modulo 16. This extra bit accounts for the different
behavior of binary depth.

## Binary capacity and an explicit witness

Let U_m(f) be the supremum of square-interval moments modulo 4^m. For f ≥ 0,
nesting gives U_(m+n)(f) ≥ U_m(f) U_n(f). Choosing digits 0 and 2 gives
U_m(f) ≥ 2^m, while the number of residues and the bound on widths give
U_m(f) ≤ 4^m. Applying the subadditive limit theorem to −log U_m(f) proves

    Λ(f) = lim_(m → ∞) U_m(f)^(1/m)
         = sup_(m ≥ 1) U_m(f)^(1/m),       2 ≤ Λ(f) ≤ 4.

No attained stationary optimizer, Bellman identity, factor-two finite-depth
estimate, or quantitative convergence rate is asserted.

The explicit binary witness uses Naslund's 25-state, 94-branch policy.
Its geometry, positive rational weights, and all weighted row inequalities
are checked in Lean. An induction constructs an actual interval alphabet
at each finite depth. At m = 10^15, its moment is at least

    2^(−f) a^(m−1) / 4,
    f = 15494199041779 / 10^14,
    a = 1430119207986461 / (5 · 10^14).

The initialization and final shrink are included in this bound. A
logarithmic certificate proves that the resulting finite alphabet meets
the required moment at α = 75806770413/10^11. The formal depth is chosen
from the singleton {10^15}, and its equality to that value is proved.
Natural powers can therefore remain symbolic without changing the witness
or adding a hypothesis.

## Numerical applications and scope

The square application combines the binary alphabet, six prime-chain
components, and two odd coupled-prime components. The chain primes are
3, 7, 11, 31, 59, and 103. The odd components use 5 · 43 and 19 · 23, with
retained words of length three and full moduli 215^6 and 437^6. Their free
multiplicities are 215^3 and 437^3.

The square witness refines Naslund's published construction at exponent
0.75806746. Replacing several retained words together in the 19 · 23 alphabet,
repositioning their intervals, adjusting rational widths, and reallocating
all nine moment exponents yield the bound 0.75806770413. Naslund's
binary transition geometry is unchanged.

The fourth- and sixth-power applications use 18 finite seed alphabets,
their canonical lifts, and exact moment inequalities. They yield exponents
4571/5000 = 0.9142 and 19059/20000 = 0.95295. All three numerical conclusions
are unconditional theorems for every N ≥ 1.

These are explicit lower bounds. The optimal exponents remain open, as do
possible improvements from other supports, interval widths, binary policies,
prime couplings, or integer constructions.

[Attribution](docs/ATTRIBUTION.md) identifies the public mathematical and
formal sources. [Proof status](PROOF_STATUS.md) and the
[verification record](docs/VERIFICATION.md) describe the mechanical checks.
