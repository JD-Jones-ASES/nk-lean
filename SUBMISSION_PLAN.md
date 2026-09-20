# nk-lean submission plan

JD authorized the private repository and Lean development on 20 September 2026.
The proposed single Palomar entry is **Interval moments for power-difference-free
sets: a general criterion, local capacity laws, and three numerical applications**.
Public release and registry intake remain separate steps requiring JD's direction.

## Mathematical case for the entry

Lead with the reusable finite-family interval-moment theorem for every k≥1.
Its hypotheses describe ordinary finite alphabets, pairwise coprime
perfect-kth-power bases, exact local moment inequalities and strict global
surplus. Its conclusion is the unconditional lower bound c N^α for every N≥1.
The selected applications are:

| Forbidden differences | Exact exponent |
|---|---:|
| Squares | 75806770413/100000000000 = 0.75806770413 |
| Fourth powers | 4571/5000 = 0.9142 |
| Sixth powers | 19059/20000 = 0.95295 |

The square improvement over the pinned Naslund witness is small but exact.
The broader mathematical contribution makes the package useful beyond its last
digits: canonical perfect-power closure and free copying from arbitrary seeds;
unit-power stabilization including singular primes; unrestricted interval-moment
multiplicativity under lexicographic graph products; the exact prime-depth law
outside binary squares; and existence of intrinsic binary capacity as a limit.
The prime-depth theorem explains where further local searches cannot help this
method. It neither bounds the unrestricted integer extremal function nor rules
out coupled-prime or binary-policy improvements.

## Comparison and evidence

Use the single master `comparator.json`, selecting 19 statements in
`Challenge.lean`. Challenge imports only Mathlib, has complete ordinary
definitions, and contains 19 intentional theorem placeholders. Solution imports
the actual proved library and certificates. Keep `definition_names` empty,
NanoDa enabled, and exactly the three standard permitted axioms.

All 19 statements and all three numerical applications compile in Lean. The
full transitive declaration audit and saved controls pass. The final independent
replay remains a required gate: statement/definition matching, the axiom policy,
Lean replay and NanoDa must each accept the exact candidate. The first aggregate
run passed all but NanoDa, which encountered an infeasible closed natural-power
reduction; the corrected representation is undergoing verification.
See `docs/VERIFICATION.md` and `docs/REPLAY_TOOLCHAIN.md` for actual run scope.

Retain the exact input files, source pins, generator replay controls and sound
Lean checkers in this repository. No access to the private Analytic-Lab is needed
to build the proofs. Keep its research commit
`916d0d604fa36c511b73f7aa214e49c16b637796` as provenance, with release backlinks
recorded in the Lab. Python and floating-point search are witness-discovery
tools, not proof oracles.

## Release sequence

1. Freeze the proved candidate; finish and record the complete independent
   replay, exact tool revisions, source/export hashes and host limitations.
2. Consolidate the private default branch, metadata, license, proof account,
   attribution and verification report. Preserve one coherent comparison
   configuration covering the 19 statements.
3. When JD authorizes public release, refresh the official intake policy and
   current numerical literature, publish the approved private candidate, and
   run the official Linux verification gate. The macOS development shim is
   unsandboxed and must not be described as that gate.
4. Submit the same approved source and metadata to Palomar. Distinguish a
   submitted or registered entry from mechanical acceptance and editorial review.
   Link the resulting release back to the Lab without removing research evidence.

## Honest boundaries and next research

No global optimality or worldwide record claim is made. The numerical boundary
near 0.7580677041313194 is for the current fixed geometry, not arbitrary supports,
reoptimized widths or policies. The strongest certified endpoint is the rational
number displayed above. The binary transition geometry remains Naslund's;
the gain comes from odd support changes, widths and a new allocation across all
nine components.

The unformalized Bellman identity and factor-two finite-depth estimates stay
outside this entry's selected claims. Further exponent research should target
new coupled-prime geometry and better binary policies, rather than depth alone
at one of the primes covered by the exact capacity law. Source attribution
belongs beside these claims: see `docs/ATTRIBUTION.md`, `DISCLOSURE.md`, and the
complete mathematical account in `PROOF.md`.
