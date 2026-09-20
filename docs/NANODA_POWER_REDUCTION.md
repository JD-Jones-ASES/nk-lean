# Keeping the finite binary depth symbolic

The square construction uses the exact finite depth 10^15. Its modulus is
4^(10^15), so expanding that natural number would require about 250 TB just
to store its bits. The mathematical proof only needs identities and bounds
involving that power.

The proof defines `binaryDepth` using `Classical.choose` from a proof that
there exists a natural number equal to 10^15. The theorem `binaryDepth_eq`
then proves that exact equality. All natural powers in the binary alphabet,
component, and coprimality proof use `binaryDepth` symbolically.

The scalar logarithmic certificate still uses the literal depth 10^15.
Its proved bound is transferred to `binaryDepth` using the equality theorem.
This representation changes no witness, numerical endpoint, or theorem
hypothesis. It uses only the already permitted `Classical.choice`; it adds
no axiom, unproved constant, or definition hole.

The relevant files are:

- [BinaryDepth.lean](../NK/Certificates/BinaryDepth.lean): exact depth and
  logarithmic certificate.
- [BinaryApplication.lean](../NK/Certificates/BinaryApplication.lean): the
  actual interval component.
- [SquareApplication.lean](../NK/Certificates/SquareApplication.lean): the
  complete square bound.
- [Binary application controls](../audit/binary-application-controls.lean).

An earlier replay at `99de2ade1fe572407d0295481b36f07167fa9e2e` passed Lean
checking but its NanoDa process was killed. A separate logging-only
diagnostic reached an attempted evaluation of the enormous closed power.
That diagnostic was stopped after the trace was obtained and was not used
as an acceptance check. The exit status alone did not establish the
operating system's reason for terminating the earlier process.

The symbolic-depth representation passed the unchanged official Comparator,
Lean kernel, and NanoDa at `409bcef149ae96f40f69d38a17cf8bd7330dee98`.
[VERIFICATION.md](VERIFICATION.md) retains that successful run's exact log,
export hash, tool versions, and host scope.
