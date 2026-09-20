# Independent replay toolchain

The private development uses Lean4.33.0 with the committed Mathlib/rk-lean pins.
The following official tool revisions were fetched and built on20 September2026:

| Tool | Revision |
|---|---|
| leanprover/comparator |3927ad383f208ae977c340a91c48ac9b497d2097|
| leanprover/lean4export |15f6055e299ad5b89345e533cc2192f4cc00f659|
| ammkrn/nanoda_lib |4c544ed4099c8227f07d5de77ad1e69fb0740a27|

Comparator and lean4export use the matching Lean4.33.0 toolchain. NanoDa is
built from its committed Cargo.lock. The official Comparator `simple_match`
control, with NanoDa enabled, passed statement comparison, the axiom policy,
NanoDa replay and the builtin Lean replay. This verifies the installation;
it is not a replay of nk-lean.

On this macOS host the official `scripts/fake-landrun.sh` development shim is
needed because Linux Landrun is unavailable. The shim provides no sandbox.
Any local result must be reported as developer-controlled source replay,
not an adversarial sandboxed verifier result. Palomar's official Linux
verification remains a separate release/intake gate.

A complete run, from the candidate checkout with these tools available, is:

```sh
COMPARATOR_LANDRUN=/absolute/path/to/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/absolute/path/to/lean4export \
COMPARATOR_NANODA=/absolute/path/to/nanoda_bin \
lake env /absolute/path/to/comparator/binary comparator.json
```

Use actual Landrun on a supported Linux host, following the pinned official
Comparator instructions. Never disable NanoDa or broaden permitted axioms
merely to obtain a successful result. `definition_names` remains empty: all
ordinary definition bodies must match, rather than being accepted as holes.

The full nk-lean run is pending. Its final result must identify the exact
candidate commit and must supersede this installation-only report explicitly.
