# Evaluation of the exponential Cole–Hopf series

Suppose `∑ i ∈ s, c i ≠ 0`, and let geometric majorants `m0`, `m1`, `mi`
majorize the heat moment series of orders `0` and `1` and the inverse of the
order-`0` series. If `r : Fin 2 → ℚ≥0` is strictly smaller than all their
radii and `x ∈ ℝ²` satisfies `|x i| ≤ r i`, then the sum of the series
`exponentialBurgersSeries s c k ν` at `x` equals the classical solution `u(x
0, x 1)`, and the heat profile `H_0(x 0, x 1)` is nonzero.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`. A geometric majorant `m` with bound `M ≥ 0` and
radii `R_i > 0` majorizes a rational power series `a` when `|coeff α a| ≤ M
∏ i, R_i ^ (-α i)` for every exponent `α`. The real heat moments are `H_n(t,
x) = ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)`, and the classical
exponential Burgers solution is `u(t, x) = -2ν H_1(t, x) / H_0(t, x)`.
