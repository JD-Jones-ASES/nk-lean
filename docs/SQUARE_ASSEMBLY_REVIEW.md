# Square assembly review

An AI-assisted source and exact-arithmetic review found no blocking mismatch
in [SquareApplication.lean](../NK/Certificates/SquareApplication.lean),
[Odd215Moments.lean](../NK/Certificates/Odd215Moments.lean), or
[Odd437Moments.lean](../NK/Certificates/Odd437Moments.lean). This note explains
the assembly checks. The accepted official replay, including the large
certificate proofs, is recorded in [VERIFICATION.md](VERIFICATION.md).

## Odd components

| Component | Full base | Root and free multiplicity | Width denominator | Moment exponent |
| --- | ---: | ---: | ---: | --- |
| 215 | 98771297640625 = 215^6 | 9938375 = 215^3 | 99999974386028 | 26536176765267 / 10^15 |
| 437 | 6964478817623209 = 437^6 | 83453453 = 437^3 | 100000118525840 | 67878931321877 / 10^15 |

Both components use `alpha = 75806770413 / 10^11`. Each full base is the
square of its displayed root. The retained-word lift has multiplicity
`(p*q)^((k−1)*e)`, which equals that root for `k = 2` and `e = 3`.
The moment comparisons therefore include the free digits exactly once.

The lift copies the intervals without rescaling. Membership in the selected
support supplies the row width bounds. Tree sortedness supplies distinct
words, so the literal row sum equals the support moment without duplicate
counting. Geometry and numerical proofs use the same tree, denominator, and
width data.

The reciprocal estimate for each width uses a positive upper bound for
`(D/w)^f`. Positivity of the true power makes that upper bound positive;
positivity of the computed lower endpoint is unnecessary. The reciprocal
inequality has the required direction. The numerical tree equalities connect
the checked sums to the same trees used for geometry.

## Nine-component transfer

The six chain components, binary component, and two odd components share the
same `alpha`. Their nine moment exponents agree with
[certificate.json](../certificates/square/certificate.json), and exact rational
addition gives

```text
sum(f_i) − alpha = 9663 / 250000000000000 > 0.
```

The bases are pairwise coprime: six prime squares, `215^6`, `437^6`, and
the binary base `4^(10^15)`. The binary depth is represented by a chosen
natural number proved equal to `10^15`; coprimality is proved symbolically
from coprimality with 4. The finite component list is nonempty.

`powerLowerBound_of_intervalMoments` consumes the constructed alphabets and
their local moment bounds. It assumes no transfer conclusion. Its result is
one positive constant valid for every integer `N ≥ 1`, with exponent
`0.75806770413` and no exponent loss.

The square construction retains Naslund's binary geometry. The improved
numerical bound uses revised odd support, widths, and moment allocation.
Neither global optimality nor optimality of the current support after
reweighting is claimed. The separate prime-depth theorem concerns ordinary
interval capacity, not an upper bound for square-difference-free sets.
