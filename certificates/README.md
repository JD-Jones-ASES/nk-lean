# Exact certificate data

These files contain the integer and rational data used by the formal proofs.
The data are checked by Lean theorems establishing the soundness of the
geometry and numerical tests.

[even.json](even.json) contains 18 finite seed alphabets for fourth and
sixth powers, with target exponents 4571/5000 and 19059/20000.
[NK/Certificates/EvenGeometry.lean](../NK/Certificates/EvenGeometry.lean)
checks every nonzero modular power arc of each seed.
[EvenMoments](../NK/Certificates/EvenMoments.lean) proves the moment
inequalities, and [EvenApplications](../NK/Certificates/EvenApplications.lean)
combines them with the transfer theorem to obtain the two bounds for every
positive integer N.

The [square directory](square/) contains the certificate and data for
exponent 75806770413/100000000000. The construction combines six prime
chains, two odd coupled-prime alphabets, and a binary policy. The odd
components have full moduli 215^6 and 437^6; their retained supports and
rational intervals are in the data files. The 437 interval file has SHA256

    fe026c70694a85892a749ea4417199325eb39ba79307c6351aa8de433585ffc0

The binary geometry is Naslund's published 25-state, 94-transition witness,
with new rational row weights and a new moment allocation. Its finite-depth
certificate includes initialization and shrinking costs. The full square
application is proved by
[NK.Certificates.square_power_bound](../NK/Certificates/SquareApplication.lean).

Search programs and numerical optimizers can suggest certificate data;
acceptance depends on exact geometry and moment proofs. Independent integer
and rational-arithmetic checks provide additional validation. Their role and
the kernel replay are described in the
[verification record](../docs/VERIFICATION.md). Public sources and credit are
listed in [ATTRIBUTION.md](../docs/ATTRIBUTION.md). These certificates prove
lower bounds and make no optimality claim.
