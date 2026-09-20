# AI assistance and responsibility

JD Jones selected the problem, directed the work, and is responsible for the
submission. The mathematical development, computational search, certificate
generation, Lean formalization, and review received substantial AI assistance.
OpenAI Codex agents carried out proof construction, exact arithmetic and
geometry checks, and reviews of theorem statements and scope. GPT 6 Pro,
Claude, and Grok also contributed mathematical suggestions, formalization
assistance, or computational tooling. AI systems are not listed as human
authors or maintainers.

Different agents reviewed the theorem statements and the agreement between
definitions and proof signatures. Independent implementations checked the
finite witnesses, including literal integer pair enumeration and a separate
rational enclosure calculation. Generator output and numerical search were
accepted only through the required exact checks and formal soundness proofs.
These roles are distinct from independent Lean and NanoDa kernel replay.

The mathematical attribution is explicit: Naslund supplies the interval
criterion and binary geometry, Krachun the ranked construction, and Jones
the formal ranked-construction dependency. Classical unit-group theory and
Mathlib supply additional arithmetic and analysis. The square improvement
comes from cooperative changes to an odd support, interval widths, and the
global moment allocation. See [ATTRIBUTION.md](docs/ATTRIBUTION.md) and the
[mathematical account](PROOF.md).

Token and monetary accounting was not retained in a form suitable for an
accurate total. No independent human peer review or endorsement by the cited
authors is recorded. Mechanical correctness, AI-assisted review, mathematical
priority, and registry status are separate matters. The
[proof status](PROOF_STATUS.md) records the verification boundary.
