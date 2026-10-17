---
article_id: af_0b8a90804d7be23ebde73e05
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Algebra.PowerSeries.KaluzaCoefficientBoundsWanted.kaluza_coeff_inv_bounds
---

# Kaluza coeff inv bounds

Combined Kaluza inverse-coefficient bounds: under
`HasPositiveLogConvexCoefficients f`, the formal reciprocal `f⁻¹` satisfies
`b₀ = a₀⁻¹` with `b₀ > 0`, and for every `n ≥ 1`,
`-aₙ / a₀² ≤ bₙ ≤ 0`, where `aₙ` and `bₙ` are the coefficients of `f`
and of the formal power-series reciprocal `f⁻¹`. This is a formal reciprocal
with no analytic convergence assumptions.

## Depends on

- [Has Positive Log Convex Coefficients](has-positive-log-convex-coefficients.md)

## Proof depends on

- [Coeff pos](coeff-pos.md)
- [Sq coeff succ le](sq-coeff-succ-le.md)

## Sources

- [MathlibExt, MathlibExt.RingTheory.PowerSeries.KaluzaCoefficientBounds](../../../../../sources/v2/MathlibExt.md)
- László Tóth, *Alternating Sums Concerning Multiplicative Arithmetic Functions*, Journal of Integer Sequences 20, Lemma `lemma_Kaluza`, `https://cs.uwaterloo.ca/journals/JIS/VOL20/Toth/toth25.tex`, lines 553–562, file sha256 `e225aae50ee869db4df08f1a24bf6448ea544ca356369d5a0c4c7321d92607d8`, span sha256 `2ad887082f5786fc8ff64b75c3a7ddb63bc0a456290eee9cb6a85acf3c868d0f`. Tóth attributes the nonpositivity of `bₙ` to T. Kaluza, Satz 3. Proves `Wanted` entry `kaluza_coeff_inv_bounds`.
