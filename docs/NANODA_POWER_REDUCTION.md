# NanoDa large-power reduction diagnosis

20 September 2026. This is a resource diagnosis, not an independent-kernel
acceptance report. It identifies a concrete evaluation triggered by the
original binary-component representation. Subsequent source changes and
their final replay results must be recorded separately.

## Official replay and diagnostic boundary

The initial complete Comparator run at
`99de2ade1fe572407d0295481b36f07167fa9e2e` passed statement/definition comparison
and the axiom policy. Its separate Lean kernel replay accepted the Solution.
The NanoDa child exited with status 137, without a reported proof-checking
panic. That exit establishes termination by SIGKILL; it does not by itself
identify the operating system's reason for the kill.

After the Odd215 numerical proof was chunked, a fresh complete Solution export
contained 232,431,308 bytes, with SHA256
`71b7f99a9508d993a675bc79ce434044b302dab8ae4732134c679b0c3a6d16e0`.
Its metadata records the same Git HEAD with uncommitted changes to
`NK/Certificates/Odd215Numeric.lean` and `scripts/generate_odd_moments.py`;
this artifact is not identified solely by the earlier commit. Direct official
NanoDa replay was also killed, after approximately 161 seconds. These runs do
not constitute successful NanoDa verification.

Tool sources remained pinned as follows:

| Tool | Revision |
|---|---|
| Comparator | `3927ad383f208ae977c340a91c48ac9b497d2097` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `4c544ed4099c8227f07d5de77ad1e69fb0740a27` |

The official NanoDa checkout and binary were left unchanged. A separate copy
at `/private/tmp/nk-nanoda-diagnostic` added only stderr logging and elapsed-time
measurements: parsing/checking stage markers, serial declaration start/end
markers with decoded names, and a marker immediately before natural-power
evaluation when the exponent exceeds one million. The original power
operation and all checking decisions remained unchanged. This modified binary
is diagnostic instrumentation, not the official verifier.

The diagnostic release build used `cargo build --release --locked --offline`.
The official binary SHA256 is
`b0c9392b6183b629d447b9a3138b50b9f2a24bcf47cf4c61b5d4a1ff05f94955`;
the diagnostic binary SHA256 is
`4018a3557878a0ce7e70ca2fef60a096a6e93e372b2fa426f681eb6cf3fee3dc`.

## Confirmed computational obstruction

On the complete export above, the diagnostic reached the following trace:

```text
[DIAG_DECL_START] 24544/44189 NK.Certificates.binary_component._proof_4
[DIAG_LARGE_NAT_POW] base_bits=3 exponent_bits=50 exponent=1000000000000000
```

The preceding declaration, `pow_right_comm`, completed. The active proof is
the component's base-equals-square identity, originally written using the
closed terms `4 ^ 1000000000000000` and `2 ^ 1000000000000000`. The trace
therefore confirms attempted enormous natural-number exponentiation in this
proof, rather than an unidentified numerical-certificate slowdown. A
three-bit base is at least four, so this exponentiation would produce at
least two quadrillion bits, approximately 250 TB of integer payload before
overhead.

The coordinator terminated this diagnostic run with SIGTERM after capturing
the trace; its recorded return code is -15 and elapsed time approximately
50 seconds. It did not complete verification. The log SHA256 is
`72387e2f4ab6807cd046ecc98a027e41dfff5f99e032a53ece19d7c2ddc67470`.
The development artifacts are `/private/tmp/nk-diagnostic-nanoda.log` and its
adjacent `.json` timing record. Those temporary paths are provenance aids,
not required build inputs.

The pinned source explains the behavior. In `src/tc.rs`, `lazy_delta_step`
calls `delta_try_nat` before its same-definition congruence attempt. Closed
natural powers can therefore reach `do_nat_bin`, whose `Pow` case evaluates
`arg1.pow(arg2)` without an exponent-size guard. Ordinary Lean acceptance of
the symbolic proof does not establish that this independent reduction
strategy will leave the same closed power symbolic.

The trace identifies a concrete resource obstruction consistent with the
earlier kills. It does not provide an operating-system OOM report, nor prove
that no other replay bottleneck exists after this one is removed.

## Source-side remedy and independent source review

The implemented change retains exactly the original depth. It proves
`∃ n : ℕ, n = 1000000000000000` by supplying that numeral, defines `binaryDepth`
with ordinary `Classical.choose`, and derives `binaryDepth_eq` from
`Classical.choose_spec`. Thus the exact value and positivity are proved;
neither is postulated. This uses the already permitted `Classical.choice`,
with no new axiom, opaque assumption, or definition hole.

The logarithmic estimate remains a literal rational certificate at depth
10^15. The generic depth-to-moment theorem is then applied to `binaryDepth`;
the equality to 10^15 is used only in its logarithmic premise. The alphabet,
component base/root, and CRT coprimality proof all use the selected depth.
The former closed-power moment theorem has been replaced, not retained as a
dependency of the new proof.

An independent read-only review covered the changes to the generated
`BinaryDepth.lean`, `BinaryApplication.lean`, `SquareApplication.lean`,
`scripts/generate_binary_depth.py`, and the binary application controls. No
mathematical weakening or hidden assumption was found. The final square
statement, nine components, moment exponents, and strict surplus are unchanged.
The updated control explicitly verifies the existence of a depth equal to
10^15 that gives both the stated component base and root.

The reviewed NK and audit source contains no remaining literal `2 ^ 10^15`
or `4 ^ 10^15` term. The exact numeral now appears in the proved depth
specification and logarithmic coefficient calculations; natural powers in
the binary application use `binaryDepth`. This is a source-level check, not
a claim that the new exported proof graph has already been independently
replayed. Fresh export and replay must confirm that elaboration has not
reintroduced the problematic evaluation elsewhere.

The change blocks conversion of the chosen depth to a numeral by ordinary
definitional reduction. It changes the witness's representation, not its
mathematical value, the square bound, or the checker.

## Subsequent official replay

After compilation and the complete declaration/control audit, the unchanged
official Comparator accepted proof commit
409bcef149ae96f40f69d38a17cf8bd7330dee98, including statement/definition matching,
the standard-axiom policy, Lean default-kernel replay and NanoDa. The complete
Solution export has 232,434,222 bytes and SHA256
e12be5029a582cad015d4e0e4fef200e0b31fdcd1b0c16651f710233a544cc71.

See VERIFICATION.md and replay/comparator-409bcef.log for the exact successful
run. The logging-only diagnostic copy was not an acceptance authority. This
later result supersedes the pending verification boundary stated at the time
of the source review, while preserving the failed runs as historical evidence.
