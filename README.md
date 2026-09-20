# Lower bounds for sets without perfect-power differences

Let $D_k(N)$ be the largest size of a subset of $\{1,\ldots,N\}$ with no
positive $k$-th-power difference. This Lean formalization proves

$$D_k(N) \ge c_k N^{\alpha_k}\qquad(N\ge1),$$

where each $c_k$ is positive and independent of $N$:

| Forbidden differences | Proved exponent $\alpha_k$ |
|---|---:|
| Squares | **0.75806770413** |
| Fourth powers | **0.9142** |
| Sixth powers | **0.95295** |

The square exponent improves Naslund's published construction at exponent
0.75806746. It uses his interval method and binary transition rules, with
changes to the odd-prime supports, interval widths, and moment exponents.
The proof builds on Krachun's directed construction and its Lean formalization
by Jones. See [sources and attribution](docs/ATTRIBUTION.md).

The main general theorem turns finite interval data into lower bounds for
sets avoiding $k$-th-power differences, for every $k\ge1$. Further theorems
show how to lift data from arbitrary moduli, describe power residues at prime
powers, and prove exact product laws for interval capacity. These laws explain
why increasing depth at a single prime cannot improve its normalized interval
capacity, except possibly for squares at the prime 2. A separate theorem proves
existence of the binary capacity limit. No optimality of the three exponents
is claimed.

## Proof and verification

- [Mathematical account](PROOF.md): statements, construction, and proof outline.
- [NKChallenge.lean](NKChallenge.lean): the 19 statements selected for comparison.
- [NKSolution.lean](NKSolution.lean): imports the complete proofs and certificates.
- [Proof status](PROOF_STATUS.md): formal coverage and limits.
- [Verification](docs/VERIFICATION.md): accepted replay, tool versions, and checks.
- [AI assistance](DISCLOSURE.md): contributions, responsibility, and review status.

The [official Linux mechanical preflight](https://github.com/JD-Jones-ASES/nk-lean/actions/runs/35540659599)
passed all 19 statements at `f324e33d76e5e578cd69c1d7909c0216df37517f`,
including statement comparison, the axiom policy, Lean kernel checking, and
NanoDa replay. Later documentation changes preserve all recorded proof and
build inputs. Palomar submission and editorial review remain separate steps.

## Build

The repository pins Lean 4.33.0, Mathlib, and its other Lean dependency.

```sh
lake exe cache get
lake build
bash scripts/audit.sh
```

The audit checks the permitted axioms and saved positive and negative controls.
Independent replay instructions are in [REPLAY_TOOLCHAIN.md](docs/REPLAY_TOOLCHAIN.md).
The project uses the MIT license.

[Submission details](SUBMISSION_PLAN.md) give the entry title, abstract, and
remaining release steps. The first Palomar submission failed because its
module names collided with those of a dependency. The submission now uses
`NKChallenge` and `NKSolution`; see the [repair record](docs/MODULE_IDENTITY.md).
