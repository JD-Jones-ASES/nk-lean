# Mathematical and formalization sources

This development formalizes and extends interval constructions for sets
without perfect-power differences. The lower bounds use established
modular constructions and arithmetic together with the explicit interval
certificates supplied in this repository.

Dmitry Krachun's
[Square-Difference-Free Sets beyond the Three-Quarter Barrier](https://arxiv.org/abs/2608.01325)
is the source of the ranked modular, word, and Chinese remainder framework.
Eric Naslund's
[Square-difference-free sets of exponent 0.75806746](https://github.com/enaslund/sarkozy-lower-bound-0.758/blob/e5d693729e23762b063a55015ad79ccaf28a3217/papers/square-difference-free-sets-of-exponent-0.75806746.tex)
supplies the interval-moment criterion, stopping-word method, odd
coupled-prime supports, and 25-state binary transition geometry used in the
square construction. The improved square certificate changes an odd
support, interval widths, and the global moment allocation. Its binary
transition geometry remains Naslund's.

The formal ranked construction uses JD Jones's
[rk-lean](https://github.com/JD-Jones-ASES/rk-lean), under the MIT license,
copyright 2026 JD Jones. The exact dependency is recorded in
[lake-manifest.json](../lake-manifest.json). Jones's
[fs-lower-bound](https://github.com/JD-Jones-ASES/fs-lower-bound) is an earlier
formalization in this line of work. The imported ranked-construction
theorems retain their original attribution; the interval transfer and
certificate proofs in this repository build on them.

Classical residue and digit constructions go back to Imre Z. Ruzsa's
[Difference sets without squares](https://doi.org/10.1007/BF02454169).
Khalid Younis's
[Lower bounds in the polynomial Szemerédi theorem](https://arxiv.org/abs/1908.06058)
provides related constructions for polynomial differences, including
perfect-degree transfer and coprime prime-power reductions. These
antecedents are not claimed as new results here.

The unit-conductor arguments use classical prime-power unit-group theory.
Keith Conrad's
[Prime-power units and finite subgroups of GL_n(Q)](https://kconrad.math.uconn.edu/blurbs/gradnumthy/primepowerunitsandGLnQ.pdf)
gives an exposition of the relevant arithmetic. Related finite-ring graph
results include Podestá and Videla's
[Waring numbers over finite commutative local rings](https://arxiv.org/abs/2212.12396),
Nguyen and Tan's
[On certain properties of the p-unitary Cayley graph over a finite ring](https://arxiv.org/abs/2403.05635),
and Podestá and Videla's
[On k-th unitary Cayley graphs over finite commutative rings: structure and decompositions](https://arxiv.org/abs/2606.06774).
Their unit-power graph results provide precedents for local decompositions.
The full power-image graphs and interval capacities used here have different
hypotheses and conclusions; those differences do not establish a priority
claim.

[Mathlib](https://github.com/leanprover-community/mathlib4) supplies the
underlying arithmetic and analysis. In particular, its ceiling-root
divisibility theorem is the arithmetic input to the canonical perfect-power
closure. This development proves the corresponding interval-copying
construction and its cardinality and moment identities.

No global optimality, worldwide record, or exhaustive novelty claim is
made. AI assistance and human responsibility are described in
[DISCLOSURE.md](../DISCLOSURE.md). Mechanical proof checking does not imply
human peer review or endorsement by the cited authors.
