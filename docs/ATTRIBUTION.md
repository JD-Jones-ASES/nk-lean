# Mathematical and formalization sources

The submission is source-based. Its center is a formal account and extension
of interval constructions for power-difference-free integer sets.

- Krachun's ranked modular construction supplies the ancestry of the ranked
  block, word and CRT framework.
- JD Jones's fs-lower-bound and rk-lean developments supply the formal ranked
  construction used here. The direct dependency is rk-lean at
  `4bf2e3a56b6a522764a4d03e5dc606c12376185e`, under the MIT licence, copyright
  2026 JD Jones. The project root retains the same licence notice. No claim
  is made that the imported RK declarations were first proved in nk-lean.
- Eric Naslund's manuscript and explicit finite witnesses at
  `e5d693729e23762b063a55015ad79ccaf28a3217` supply the interval-moment method,
  odd mixed-prime supports and binary transition geometry used in the square
  application. The square source is
  https://github.com/enaslund/sarkozy-lower-bound-0.758 .
- Claude suggested the initial even-k port. GPT 6 Pro produced the user-supplied
  CONSULT.md and even_power_research_package.zip, which informed
  the general even-power direction. Analytic-Lab P0177 independently checked
  the supplied targets and developed conductor/closure extensions.
- Analytic-Lab P0177–P0180 contain the written general arguments, improved
  square/fourth/sixth certificates, binary capacity work, independent replays,
  and precise local search boundaries. Preserve their release pins in the
  eventual submission metadata.
- Mathlib already defines the ceiling root and proves the divisibility
  adjunction used in NK.PerfectPowerClosure. The arithmetic primitive is not
  claimed new. The free-copy interval application uses that existing result.

AI assistance and JD's responsibility must be described honestly in release
metadata. Mechanical verification and AI review are distinct from human peer
review, editorial endorsement and mathematical priority.

Relevant arithmetic and graph precedents include Keith Conrad's exposition
of prime-power unit groups; Younis, *Lower bounds in the polynomial Szemeredi
theorem*, arXiv:1908.06058 (perfect-degree transfer and coprime compression);
Podesta–Videla, *Waring numbers over finite commutative local rings*,
arXiv:2212.12396 (coprime unit-power Cayley graph blow-ups); Nguyen–Tan,
*On certain properties of the p-unitary Cayley graph over a finite ring*,
arXiv:2403.05635 (a singular-prime unit-graph special case); and
Podesta–Videla, *On k-th unitary Cayley graphs over finite commutative rings*,
arXiv:2606.06774 (including the sixth-power directed9-cycle example).
Their unit-only results and hypotheses differ from the full-image,
multiple-depth interval-capacity statements here. These antecedents prevent
an attribution of every local compression ingredient to this development.
The supplied consultation already proposed the prime-local moment barrier;
its independent proof and formalization here do not establish worldwide novelty.
