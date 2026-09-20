# Research data and formal status

These are exact research witnesses, copied from the private Analytic-Lab.
They are data for the formal development, not assumptions or Lean proofs.

- `even.json`: P0177 fourth/sixth-power integer seed tables, target exponents
  4571/5000 and 19059/20000. `NK/Certificates/EvenGeometry.lean` checks every
  full modular power arc for these 18 literal seeds by kernel reduction.
- `square/`: P0180 certificate and data pinned at Analytic-Lab commit
  `916d0d604fa36c511b73f7aa214e49c16b637796`, target exponent
  75806770413/100000000000. The odd437 witness SHA256 is
  `fe026c70694a85892a749ea4417199325eb39ba79307c6351aa8de433585ffc0`.
  The binary geometry is Naslund's published 25-state, 94-transition witness
  at `e5d693729e23762b063a55015ad79ccaf28a3217`, with a new exact
  allocation/growth certificate. Credit and scope remain as recorded in
  the data and `docs/ATTRIBUTION.md`.

The square witnesses have independent integer geometry and numerical replays
recorded in the Lab; the numerical application is not yet closed in Lean.
No global optimum is claimed. The finite geometry, rational-power evaluator,
full transfer, and final unconditional applications are separate proof gates.
