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
- The user-supplied CONSULT.md and even_power_research_package.zip informed
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
