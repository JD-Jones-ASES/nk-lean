# Exact finite certificate replay

The finite data are untrusted literals. Soundness is proved separately for
ordered alphabets, retained digits, binary policies, fixed-point arithmetic
and the certificate tree. All finite proof obligations use ordinary kernel
reduction, including `decide +kernel`; no native evaluation axiom is allowed.

## Geometry

Odd215 has4,913 rows and Odd437 has19,683 rows. The balanced trees store
common prefixes and minimum interval starts. Literal row bounds, every node
summary and strict key ordering are checked. Fixed residue masks are checked
against the full nonzero modular power image once per prime.

A source query may skip a target subtree only if the source interval ends
before its minimum start, or its first unequal digit rules out every power
arc into that prefix. Otherwise it checks both children. The soundness theorem
refines the original geometric checker. Every source chunk uses the same
**full target tree**; checking only the target subtree with the same name
would miss cross-child arcs and is explicitly rejected by a saved control.

Monolithic kernel reduction exhausted practical memory: the profiled215
geometry process reached12.8GB. The final generator therefore partitions
source rows into76/77-row chunks (64 for215,256 for437). Generic proved
assembly combines their predicates, row validity and sortedness without
recomputing root-wide queries. This changes verification cost, not the data
or mathematical condition.

## Numerical moments

The evaluator uses exact natural-number endpoints at scale10^24, proved
outward rounding, finite log and exponential series, and three squarings
for each odd width. The one-sided reciprocal theorem retains exactly the
original lower endpoint S²/upper. It avoids computing a lower bound on the
reciprocal power that the required moment inequality never uses.

Odd437 has19,683 distinct widths;215 has1,861 distinct widths among its4,913
rows. The437 calculation is divided into256 chunks of76/77 widths. Each
chunk proves validity and an exact natural lower sum; generic congruence
lemmas assemble the parent sums. Python computes candidate literals, which
are checked in Lean. The root sum is
12261338816591850911384777125; the final scaled natural comparison has
positive surplus1424402168362429321833002. These integers concern the local
437 moment certificate, not the global exponent surplus.

An inexpensive Python-only replay reproduces the production numeric wrapper
without overwriting it or launching Lean. From the repository root:

```sh
python3 scripts/generate_chunked_odd_moments.py --q 437 --out scratch/odd437-numeric-normal
python3 -O scripts/generate_chunked_odd_moments.py --q 437 --out scratch/odd437-numeric-optimized
cmp NK/Certificates/Odd437Numeric.lean scratch/odd437-numeric-normal/Odd437NumericChunked.lean
cmp scratch/odd437-numeric-normal/Odd437NumericChunked.lean scratch/odd437-numeric-optimized/Odd437NumericChunked.lean
```

Both byte comparisons passed. The reproduced production file has SHA-256
`d84ce9c5c3c8f49f3cf3822e9c889774c48d1a0e5629e1cb14a8871ce5e20266`.
Each output directory also contains `report.json` with the exact sum, upper
endpoint, multiplicity and comparison surplus. Compare the Lean files rather
than report bytes: reports include output paths and elapsed time.

The production generator's arithmetic and generic proof assembly were checked
against the earlier audited prototype. Changes concern portable paths,
documentation and serial elaboration. Separate normal and `-O` mutation
controls rejected an altered literal width, an altered flat-data width and an
incorrect root alias before creating any output. Python success remains a
reproducibility check; the numerical proof still comes from Lean replay.

The main generators are:

```sh
python3 scripts/generate_odd_geometry.py --q 215 --emit
python3 scripts/generate_odd_geometry.py --q 437 --emit
python3 scripts/generate_odd_moments.py
```

They preserve the locked flat input data and emit the chunked production
checks. Run the large Lean builds sequentially on memory-constrained hosts:

```sh
lake build NK.Certificates.Odd215Geometry
lake build NK.Certificates.Odd215Moments
lake build NK.Certificates.Odd437Numeric
lake build NK.Certificates.Odd437Geometry
lake build NK.Certificates.Odd437Moments
lake build NK.Certificates.SquareApplication
```

The complete Odd215 geometry and component, and the complete chunked
Odd437 numerical certificate, have passed. Odd437 geometry and the final
unconditional square assembly have also compiled successfully. Generated large modules disable asynchronous
theorem elaboration so bounded kernel checks do not overlap in memory.
PROOF_STATUS.md and VERIFICATION.md must record the actual final outcomes.
Generators, Python controls and an external exact research replay do not by
themselves establish that the full Lean square application has closed.
