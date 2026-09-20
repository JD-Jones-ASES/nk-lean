# Proposed comparison surface

The submission should lead with one reusable theorem and its three numerical
applications, with structural results explaining which local searches can
improve the construction. The finite data and checking algorithms belong in
Solution; they must not appear as unproved hypotheses of the numerical claims.

## Headline statements

1. General finite-family interval-moment transfer, for every k≥1 and α≥0:
   ordinary finite alphabets on pairwise coprime perfect-kth-power moduli,
   positive widths below1, full modular kth-power arc ordering, local moment
   bounds, and strict sum-of-moment-exponents surplus imply the all-N lower bound.
2. Square differences: exponent75806770413/100000000000 (proved).
3. Fourth-power differences: exponent4571/5000 (proved).
4. Sixth-power differences: exponent19059/20000 (proved).

The lower-bound predicate quantifies over every positive N and a finite subset
of{1,…,N}, excludes every nonzero perfect-power difference, and supplies one
positive constant independent of N. Exponents are exact rational numbers.

## Explanatory companions

- Canonical perfect-power closure, zero detection and exact free copying from
  arbitrary seed moduli, including singular-prime examples.
- Retained-digit forward graph maps and exact CRT fiber/moment counts.
- Binary four-branch geometry, genuine finite-policy growth, and a capacity
  defined intrinsically from actual interval alphabets. Its finite-depth
  roots converge to their supremum, between2 and4.
- Full unit-conductor stabilization, exact graph lexicographic capacity, and
  the prime-depth capacity formula are proved and audited. The prime-depth
  statements cover arbitrary alphabets for all f≥0 outside (p,k)=(2,2).

The binary lower certificate is finite: depth10^15 and an explicit rational
weighted policy. The modulus is treated symbolically, not expanded into an
integer literal. It does not assume a stationary optimizer or a Bellman
identity. Capacity bounds concern this interval method, not a global upper
bound for the Furstenberg–Sárközy problem.

## Packaging

Challenge.lean imports only Mathlib and contains 19 selected theorem
statements over complete ordinary mathematical definitions. Its definitions can use the same
fully qualified names and signatures as the independently developed library;
Solution then supplies the actual declarations through its imports. Check this
layout against Comparator on the exact candidate commit before release.
The current draft has239 lines and9,186 bytes, below the official limits;
recheck these counts on the final candidate.

No definition holes are permitted: comparator.json keeps definition_names
empty so all ordinary definition bodies are compared transitively.

Keep the numerical results together with the general transfer. Put proof
architecture, certificate provenance, credit, numerical scope and the remaining
search opportunities in the paper/README rather than adding implementation
hypotheses to the statement. Retain Krachun/Jones/Naslund attribution and separate
standard unit-group/Mathlib ingredients from this project's new constructions.

Public release and Palomar intake are separate from completion of the private
proof package. Neither has occurred.
