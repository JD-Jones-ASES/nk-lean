# nk-lean development rules

This is the user-authorized private spin-out of Analytic-Lab P0177–P0180.
Read README.md and SUBMISSION_PLAN.md. Preserve full intended scope; distinguish
research certificates from formal proofs. All target theorems must be genuine
unconditional applications, not hidden assumptions or redefinitions.

Use pinned, attributed dependencies. Only permitted standard Lean axioms may
occur transitively in submitted proofs. No sorry in proofs, custom axioms, native_decide,
unsafe/partial proof substitutes or weakening of the mathematical statement.
Record actual builds and axiom checks. Keep optional hosted CI controlled and
run independent release gates on a concrete exact commit. Do not publish the
private repository or register a submission without the user's release direction.

Coordinate file ownership between agents. Keep mathematical discovery in
Analytic-Lab and copy only curated, pinned research evidence into this project.

Challenge.lean may contain explicitly labelled theorem placeholders for the
standard independent comparison protocol. It must never be imported by Solution
or NK. Mathematical definitions in Challenge must have complete ordinary bodies.
