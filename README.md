# nk-lean

Work in progress toward a coherent formalization of interval-moment constructions
for sets avoiding power differences. This repository is private development,
not a completed Palomar submission. No new theorem is claimed Lean-verified yet.

The research inputs are Analytic-Lab P0177–P0179, currently pinned at
`02e467c93722e9cfc0dcc670466901b4391c2868`. They contain written proofs and
independent exact certificates for square exponent 0.75806759, fourth-power
exponent 0.9142, and sixth-power exponent 0.95295. Further square research is
active; the release exponent will be selected only from rigorously checked
certificates, not floating-point search outputs.

The intended center is a general interval-moment transfer through arbitrary
moduli, conductor compression, and the exceptional binary square recursion.
Naslund's construction and the Krachun–Jones ranked/CRT lineage retain explicit
attribution. The user's supplied consultation informed the even-power work.

See [SUBMISSION_PLAN.md](SUBMISSION_PLAN.md) for the complete target and release
gates. Development status must distinguish written mathematics, exact Python/C++
certificates, and kernel-checked Lean proofs.
