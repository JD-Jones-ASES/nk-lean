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

Odd437 has 19,683 distinct widths; Odd215 has 1,861 distinct widths among
its 4,913 rows. Both production numerical wrappers are now chunked: 64 chunks
for 215 and 256 for 437, each containing 76 or 77 widths. Each chunk proves
validity and an exact natural lower sum; generic congruence lemmas assemble
the parent sums. Python computes candidate literals, which Lean must check.

| Component | Exact root lower sum | Local scaled comparison surplus |
|---|---:|---:|
| Odd215 | 4088483319740695586635924782 | 56253318137051129930389 |
| Odd437 | 12261338816591850911384777125 | 1424402168362429321833002 |

These integers concern the individual local moment certificates, not the
global exponent surplus. Odd215's input data and public moment inequality
are unchanged; its former monolithic proof is now assembled from chunks.

An inexpensive Python-only replay reproduces both production numeric wrappers
without overwriting them or launching Lean. From the repository root:

```sh
for q in 215 437; do
  python3 scripts/generate_chunked_odd_moments.py --q "$q" --out "scratch/odd$q-numeric-normal"
  python3 -O scripts/generate_chunked_odd_moments.py --q "$q" --out "scratch/odd$q-numeric-optimized"
  cmp "NK/Certificates/Odd${q}Numeric.lean" "scratch/odd$q-numeric-normal/Odd${q}NumericChunked.lean"
  cmp "scratch/odd$q-numeric-normal/Odd${q}NumericChunked.lean" "scratch/odd$q-numeric-optimized/Odd${q}NumericChunked.lean"
done
```

All byte comparisons passed. The reproduced production SHA-256 values are:

- Odd215Numeric: `ff1a13b2073ee32937e2bbe4be74fca58c2a6e7532082feb49ee04073cd00bfb`
- Odd437Numeric: `d84ce9c5c3c8f49f3cf3822e9c889774c48d1a0e5629e1cb14a8871ce5e20266`

Each output directory contains `report.json` with the exact sum, upper
endpoint, multiplicity and comparison surplus. Compare the Lean files rather
than report bytes: reports include output paths and elapsed time.

The production generator's arithmetic and generic proof assembly were checked
against the earlier audited prototype. The main generation path now dispatches
both components to this chunked generator and leaves their application
wrappers unchanged. Separate normal and `-O` mutation controls rejected an
altered literal width, an altered flat-data width and an incorrect root alias
for each component before output creation. Python success is reproducibility
evidence; the numerical proof still comes from Lean replay.

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
lake build NK.Certificates.Odd215Numeric
lake build NK.Certificates.Odd215Moments
lake build NK.Certificates.Odd437Numeric
lake build NK.Certificates.Odd437Geometry
lake build NK.Certificates.Odd437Moments
lake build NK.Certificates.SquareApplication
```

Generated large modules disable asynchronous theorem elaboration so bounded
kernel checks do not overlap in memory. The production Odd215 numerical
representation has changed; this document records its generator replay,
not completion of the post-change aggregate or independent verifier checks.
PROOF_STATUS.md and VERIFICATION.md record actual Lean, Comparator and NanoDa
outcomes. Generator controls and an external exact research replay do not
substitute for those checks or establish that NanoDa's resource issue is resolved.

## Chosen-depth generator freshness

At proof commit 409bcef149ae96f40f69d38a17cf8bd7330dee98, an independent driver
intercepted output writes from scripts/generate_binary_depth.py and reproduced
all 2,689 production bytes under normal Python and -O. Production SHA256:
61947f19be9647b5be5b1de04bd2c4346ea6677c781fa62e46a76b7a9719deed.
The normal/optimized records are retained in docs/replay. This is generator
freshness evidence; independent-kernel acceptance is recorded in VERIFICATION.md.
