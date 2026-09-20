# Sources and submission requirements

The source and policy review uses the following fixed revisions:

| Source | Revision |
|---|---|
| Naslund's square-difference construction | `e5d693729e23762b063a55015ad79ccaf28a3217` |
| The ranked construction in rk-lean | `4bf2e3a56b6a522764a4d03e5dc606c12376185e` |
| PalomarPolicy | `792c7c0b9e798bd02719e795ef11fa2b5929e067` |
| PalomarSubmission | `3561d237dcc4b28482558ad28a64d767d7cc8615` |

Naslund supplies the square interval method, retained odd supports, and
25-state binary transition rules. The present construction changes odd
supports, widths, and moment allocations, and proves a general transfer
criterion for positive k. The direct rk-lean dependency supplies the earlier
ranked construction. [ATTRIBUTION.md](ATTRIBUTION.md) records the public sources
and distinguishes standard arithmetic ingredients from these applications.

The [current policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md)
requires a public repository and exact commit, pinned Lean dependencies,
a Mathlib-only Challenge, a proved Solution, one comparison configuration,
v0.4 metadata, and a matching SPDX license. The project name in the metadata
is the public entry title; the description is its abstract.

The selected 19 statements cover the interval criterion, arithmetic lifting,
unit conductors, capacity laws, and the three numerical bounds. Their full
scope is explained in [PROOF.md](../PROOF.md). Definitions are compared
without holes. The permitted axioms are `propext`, `Classical.choice`, and
`Quot.sound`; NanoDa is enabled.

The complete local mechanical replay is recorded in
[VERIFICATION.md](VERIFICATION.md). Palomar performs its own Linux checks and
editorial review. A local pass does not establish registration or endorsement.
The source and metadata requirements should be refreshed at actual intake.
