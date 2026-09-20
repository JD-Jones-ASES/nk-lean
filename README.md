# nk-lean

A private development of interval-moment constructions for sets avoiding
perfect-power differences. The intended Palomar package centers on a general
transfer theorem, arbitrary-modulus/conductor reductions, binary capacity,
and improved square, fourth-power and sixth-power lower bounds.

The research is pinned at Analytic-Lab commit
`916d0d604fa36c511b73f7aa214e49c16b637796` (P0177–P0180).
The current independently checked Lab square exponent is **0.75806770413**;
the fourth and sixth exponents are **0.9142** and **0.95295**. These are written
mathematics plus exact finite certificates. Their unconditional Lean proofs
are under development, and no Palomar submission has occurred.

The full general finite-family interval-moment transfer theorem now compiles,
along with canonical closure/free-copy lifting and the underlying word, rank,
CRT and stopping arguments. [PROOF_STATUS.md](PROOF_STATUS.md)
separates this formal coverage from outstanding work. [SUBMISSION_PLAN.md](SUBMISSION_PLAN.md)
records the full mathematical target and release gates; [attribution](docs/ATTRIBUTION.md)
credits Krachun, Jones, Naslund, the supplied consultation and Mathlib.

Build with `lake build` using the committed Lean4.33.0 toolchain and exact
Mathlib/rk-lean dependency pins. The full project is MIT licensed.
