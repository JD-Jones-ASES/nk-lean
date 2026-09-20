# Lean reuse and Palomar contract audit

This is the initial source and policy audit. Its proposed theorem list records
an earlier planning stage, including the earlier square exponent and stronger
binary targets. The current comparison surface is `Challenge.lean`;
`STATEMENT_DESIGN.md` and `PROOF_STATUS.md` record its actual scope and status.

Read-only audit on 2026-09-20. Sources were fetched from the explicitly named
GitHub projects into this directory; no project below `~/Documents/repos`
was inspected. No Lean build, Comparator run, or NanoDa replay was performed
in this audit. Statements about interfaces below come from pinned source,
not from a newly replayed build.

## Pins and compatibility

| Source | Exact revision | Lean | Mathlib |
|---|---|---|---|
| [rk-lean](https://github.com/JD-Jones-ASES/rk-lean/tree/4bf2e3a56b6a522764a4d03e5dc606c12376185e) | `4bf2e3a56b6a522764a4d03e5dc606c12376185e` | 4.33.0 | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| [ns-lean](https://github.com/JD-Jones-ASES/ns-lean/tree/035e9b0c147630e35631e4401433660f695d1fba) | `035e9b0c147630e35631e4401433660f695d1fba` | 4.33.0 | `db584cd6d46c92f209a44c0f1c829460d327499d` |
| [fs-lower-bound](https://github.com/JD-Jones-ASES/fs-lower-bound/tree/d1294519dfdcc5f7e139e77336a7d042f390b9e7) | `d1294519dfdcc5f7e139e77336a7d042f390b9e7` | 4.33.1 | `0df444a360eaa60ab8c11dca51a86af692955474` |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/blob/792c7c0b9e798bd02719e795ef11fa2b5929e067/CONTRIBUTING.md) | `792c7c0b9e798bd02719e795ef11fa2b5929e067` | — | — |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/blob/3561d237dcc4b28482558ad28a64d767d7cc8615/toolchains.json) | `3561d237dcc4b28482558ad28a64d767d7cc8615` | minimum 4.28.0 | — |

The original `JS-Jones-ASES/fs-lower-bound` URL returned authenticated HTTP
404; the intended source exists under **JD-Jones-ASES**. Its Lean project is
under `note/anc/lean`, not the repository root. Both Mathlib revisions'
`lean-toolchain` files were independently fetched and agree exactly with
the table. The minimum was saved as `policy-toolchains.json` at its pinned
PalomarSubmission revision.

The simplest reuse route is Lean 4.33.0 with the common rk/ns Mathlib pin.
The general-k RK code already subsumes the square-only fs transfer, so an
fs dependency is not needed merely to support k=2. If another toolchain is
chosen, port the reused sources and actually rebuild them; do not treat
the two patch versions as an already checked compatible combination.

## Decisive existing interfaces

All the following RK names are in namespace `KthPower`. Files below are
relative to the pinned `rk-lean/` directory.

### Full power image and rank convention

`RK/Defs.lean:24` defines:

```lean
def IsNonzeroPowerMod (k m d : ℕ) : Prop :=
  d % m ≠ 0 ∧ ∃ z < m, z ^ k % m = d % m
```

This includes nonunits. `diffMod m a b = (b + m - a) % m` is b−a for the
residues used in the statements. `RK/RankedBlocks.lean:38` defines:

```lean
def RankedBlock (k P : ℕ) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ) : Prop :=
  (∀ x ∈ C, x < P) ∧ (∀ x ∈ C, h x < H) ∧
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
    IsNonzeroPowerMod k P (diffMod P x y) → h y < h x
```

Ranks **decrease** along power arcs. P0177's interval coordinates increase;
reverse a height-H discretized rank by H−1−r when using this interface.
`RankedBlock.of_validRankedSupport` (`RankedBlocks.lean:90`) turns the
decidable list certificate into this semantic predicate:

```lean
theorem RankedBlock.of_validRankedSupport (k m H : ℕ)
    (sup : List (ℕ × ℕ)) (hv : ValidRankedSupport k m sup H) :
    RankedBlock k m (supportFinset sup) (rankOf sup) H
```

### Arbitrary perfect-power base: already proved

`RK/LemmaB.lean:230` is precisely the root cancellation needed in the new
first-difference argument, with no squarefree hypothesis:

```lean
theorem word_step3_root_split (k n P j z : ℕ)
    (hk : 1 ≤ k) (hP : P = n ^ k)
    (hdvd : P ^ j ∣ z ^ k) :
    ∃ u, z ^ k = P ^ j * u ^ k
```

`RK/LemmaB.lean:413` packages the full first differing digit and rank drop:

```lean
theorem word_rank_drop_of_pow (k n P : ℕ) (hk : 1 ≤ k)
    (hP : P = n ^ k) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock k P C h H) (L : ℕ) (hL : 1 ≤ L)
    (X Y z : ℕ) (hX : X ∈ wordBlock P L C)
    (hY : Y ∈ wordBlock P L C) (hXY : X ≠ Y) (hz : 0 < z)
    (hcong : z ^ k % P ^ L = diffMod (P ^ L) X Y) :
    wordRank P L H h Y < wordRank P L H h X
```

`RK/LemmaB.lean:465` and `:531` give:

```lean
theorem lemmaB_pdf (k n P : ℕ) (hk : 1 ≤ k) (hP : P = n ^ k)
    (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock k P C h H) (L : ℕ) (hL : 1 ≤ L) :
    PowerDifferenceFree k (integerSet P L H C h)

theorem lemmaB_card_le_D (k n P : ℕ) (hk : 1 ≤ k)
    (hP : P = n ^ k) (C : Finset ℕ) (h : ℕ → ℕ) (H : ℕ)
    (hC : RankedBlock k P C h H) (hH : 1 ≤ H)
    (L : ℕ) (hL : 1 ≤ L) :
    C.card ^ L ≤ D k ((P * H) ^ L)
```

Useful elementary companions are `wordBlock_card`, `integerSet_card`,
`integerSet_subset`, `le_D_of_pdf`, and the `RK/DiffMod.lean` lemmas.
These can save the arithmetic work; they do **not** by themselves establish
the new interval-moment bound. The old construction charges H at each
word digit. The P0177 sharp transfer uses a shared rank cost after stopping
at a common interval scale; this extra argument must actually be proved.

### CRT already proved; arbitrary-modulus closure needs new formalization

`RK/LemmaC.lean:142` proves `lemmaC`: coprime ranked blocks of heights Hp,Hq
glue to modulus P·Q, support `crtBlock P Q Cp Cq`, sum rank
`hp (x % P) + hq (x % Q)`, and height Hp+Hq−1. The assumptions are
`Nat.Coprime P Q`, both `RankedBlock` hypotheses, and positive heights.
`crtBlock_card` at `:234` proves the product count; `glueList_rankedBlock`
and `glueList_card` handle finite lists.

In contrast, `RK/LemmaA.lean:551` has the explicit assumptions
`Squarefree m`, `2 ≤ m`, `1 ≤ k`, and `1 ≤ e`. It lifts modulus m to
m^(k·e) using constrained k-spaced digits. `ValidPool` also requires
squarefree seed moduli. Do not delete these assumptions. P0177's closure
B_k(d), its zero-detection equivalence, and its copying theorem for
arbitrary d are new formalization work.

### Asymptotics: useful code, not the desired all-N statement

`RK/Asymptotics.lean:45` gives `D_mono`. At `:516`, the **private** theorem
`passage` takes

```lean
(hstage : ∀ L : ℕ, 1 ≤ L → C ^ L ≤ D k (B ^ L))
(hρ : ρ < Real.log C / Real.log B)
```

with B,C≥2, and concludes eventually `(N : ℝ)^ρ ≤ D k N`.
It is private, so port/adapt its proof rather than relying on a stable
exported identifier. The logarithmic floor argument already exposes the
lost constant B^(−α), then absorbs it with a strict exponent loss. A new
generic all-N passage can retain that constant and handle small N by a
singleton, but it still needs its own proof.

The public `directed_pointwise_internal` (`RK/Main.lean:30`) and
`directed_liminf_internal` (`:23`) require a `ValidPool`, hence squarefree
seed moduli. They prove eventual bounds below the old pool exponent or its
liminf form. They are not an exact all-N constant theorem for the new data.

### Numeric and finite certificates

`RK/Numeric.lean:80` and `:92` prove:

```lean
theorem lt_log_div_log (a b : ℝ) (p q : ℕ) (_ha : 2 ≤ a)
    (hb : 2 ≤ b) (hq : 0 < q) (h : b ^ p < a ^ q) :
    (p : ℝ) / q < Real.log a / Real.log b

theorem log_div_log_lt (a b : ℝ) (p q : ℕ) (ha : 2 ≤ a)
    (hb : 2 ≤ b) (hq : 0 < q) (h : a ^ q < b ^ p) :
    Real.log a / Real.log b < (p : ℝ) / q
```

These reduce a **single log ratio** to a natural-power comparison. Their
existing comparisons have exponents of a few thousand; ordinary `decide`
checks them. They are not a preexisting proof of the interval sums,
fractional powers, binary row inequalities, or atanh/Taylor enclosure
algorithm in P0179. Raising a rational width to a denominator of 10^12
and deciding a gigantic power is not a practical substitute for proving
the fixed-point enclosure routine correct.

Both rk/ns use ordinary `decide` for their small finite certificates and
audit the transitive axioms of their project constants. For P0179 the
77-million-edge odd component needs a proved efficient certificate checker
or a factored mathematical certificate. The successful external Python/C++
replays are evidence and test oracles, not Lean proof terms.

## What ns-lean and fs actually add

In `ns-lean`, namespace `NS`:

* `NS/Code.lean:28` proves `code.card = 10` and `:32` proves that two words
  in the supplied code whose coordinate differences are all 0 or 1 agree.
* `NS/Lift.lean:195`, `:201`, `:213` prove `lift_card`, `lift_allBelow`,
  `lift_sdf`. Precisely, a set B of polynomials over F3 below even degree m
  lifts to a square-difference-free set below degree m+8, with cardinality
  810·|B|.
* `NS/Main.lean` proves the explicit 810-element degree<8 example, both
  infinite families, and the conjecture refutation for every admissible
  n≥8 with 4 dividing n. `NS/Asymptotics.lean:109` proves its liminf bound.

This is useful if the final project includes the function-field bridge,
but it has no generic Frobenius stripping theorem and no integer interval
transfer. P0177's identity
`D_{q,p^a*l}(n) = q^(n-ceil(n/p^a)) D_{q,l}(ceil(n/p^a))`
requires new finite-field/Frobenius and graph-component arguments. Keep it
as a secondary module if it would delay the three integer conclusions.

The fs Lean development has global theorem names `sdf_liminf_ge`,
`sdf_pointwise`, and `alphaInf_gt : (0.7537 : ℝ) < alphaInf` in
`FsLowerBound/Statements.lean`. It has the analogous square-only blocks,
CRT, numeric lemmas, and asymptotic passage. RK's general-k versions are
the preferable reuse layer for this project; attribution should still
explain their ancestry. All three named projects have MIT licence files;
retain the applicable copyright and licence notices when copying material.

## Coherent final formal statements

Keep one Mathlib-only `Challenge.lean`, with ordinary definitions and
theorems that state the actual mathematical conclusions. Proposed theorem
names below are a design recommendation, not existing proved Lean names.

1. **`interval_moment_lower_bound`.** For k≥2, a nonempty finite family of
   pairwise coprime perfect kth-power bases b_i>1, ordered interval alphabets
   with widths strictly between zero and one, f_i≥0 and α≥0, if
   `sum_x w_ix ^ f_i ≥ b_i ^ α` for each i and `sum_i f_i > α`, conclude
   an all-N kth-power-free lower bound.
2. **`closure_zero_detection` / `closure_interval_lift`.** For d≥2,
   B_k(d)=product p^(k ceil(v_p(d)/k)), prove d|z^k iff B_k(d)|z^k, and the
   resulting copied alphabet and moment factor B_k(d)/d. This records the
   actual arbitrary-modulus extension instead of disguising it as a
   dropped squarefree hypothesis.
3. **Three direct headlines:** `square_lower_bound`, `fourth_lower_bound`,
   `sixth_lower_bound`, at exact rational exponents 75806759/100000000,
   4571/5000, and 19059/20000. Each should have the same transparent form:

```lean
∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    (∀ a ∈ A, ∀ z : ℕ, 0 < z → a + z ^ k ∉ A) ∧
    c * (N : ℝ) ^ α ≤ (A.card : ℝ)
```

   Alternatively use a precisely defined D_k maximum, provided the
   statement says the same thing. The fixed data, finite-depth binary
   policy, numerical enclosures, and moment surplus belong in Solution.
   Do not expose conditional certificate assumptions in place of the
   three unconditional numerical claims.
4. **Structural P0177 results:** conductor compression including p|k,
   exact prime-local lexicographic factorization except (p,k)=(2,2), and
   its moment product consequence. State the exception in every public
   theorem. These explain both the even-power gains and why binary squares
   retain additional depth freedom.
5. **Structural P0178 results:** define the ordinary interval optimum U_m(f)
   modulo 4^m and capacity Λ(f). For f>0, prove the exact recursion,
   `U_m U_n ≤ U_(m+n) ≤ 2 U_m U_n`, existence of Λ, and
   `U_m ≤ Λ^m ≤ 2 U_m` for m≥1. This is a compact central conclusion with
   a quantitative finite-horizon interpretation. State finite rational
   policy completeness separately for rational f>0; do not assert an
   attained optimal policy, differentiable optimal capacity, or efficient
   convergence. The Collatz-Wielandt statement and cut reductions are
   valuable secondary declarations after this core is proved.

This presents one coherent project: a general interval transfer, exact
arithmetic/conductor reductions, binary capacity, and three concrete
integer bounds. Each accepted comparator declaration must actually have
a proof. It is better to keep unfinished ambitious statements out of the
claimed formal coverage until they are proved, while still documenting
the complete planned project explicitly.

## Current submission gates and provenance

The authoritative checked source is the pinned Palomar CONTRIBUTING.md.
The following gates affect the new project immediately:

* An ordinary submission is a **public** GitHub repository, full 40-digit
  commit, explicit Comparator path, and at most 500 MiB source checkout.
  A private nk repository is suitable for development; submitting it is
  not yet possible under this contract.
* Exactly one Lakefile, a committed manifest, and exact Lean/Mathlib
  toolchain agreement. Git dependencies must use public credential-free
  GitHub HTTPS URLs and full lowercase commit pins. No source submodules,
  LFS pointers, or compiled artifacts outside `.lake`.
* Challenge's transitive imports may contain core and authenticated
  canonical Mathlib/Tau Ceti/CSLib sources only. Importing RK or NS in the
  Challenge is prohibited even if those projects were registered before.
  They may be used by the Solution. Challenge has a hard 100 KiB/1000-line
  limit, with a warning above 32 KiB/300 lines.
* Solution must match the Challenge declarations through Comparator. Only
  `propext`, `Quot.sound`, `Classical.choice` are permitted axioms. Palomar
  forces NanoDa replay regardless of a submitted `enable_nanoda` value.
  `native_decide`-generated axioms do not meet this condition.
* Root licence must have one unambiguous SPDX identity matching metadata.
  Metadata needs a concise exact abstract, human authors and responsible
  maintainers, mathematical classifications, automation methods, an honest
  pre-submission review status, and source relationships.
* For this package, **source-based** is the honest overall origin: it
  adapts Naslund's published interval/binary work and develops the supplied
  consultation and Lab results. Preserve Naslund, consultant, predecessor
  project and human responsibility credits. Put mathematical sources in
  `sources` and reused Lean developments in `related_formalizations` with
  exact pins. Do not mix `type: original-proof` with substantive `adapts`
  or `formalizes` entries; that combination fails the current origin rule.
* Mechanical verification plus an AI review finding no blocking issue are
  required. Such review is not human peer review, endorsement, or a novelty
  theorem. Submission and registration are distinct: registering additionally
  publishes the record and immutable source-preservation tags.
* Before an eventual agent submission, read the live submission server's
  `llms.txt`. It was not needed or used here because this task did not submit
  anything. Author/maintainer authorization, push-access verification, and
  final registration consent are separate protocol steps.

The mathematical target is substantially stronger than a repackaging of
rk-lean: the new transfer handles interval weights and arbitrary seed
moduli; the numeric targets exceed the named predecessor results. Nothing
in this audit establishes global optimality or a worldwide record.
