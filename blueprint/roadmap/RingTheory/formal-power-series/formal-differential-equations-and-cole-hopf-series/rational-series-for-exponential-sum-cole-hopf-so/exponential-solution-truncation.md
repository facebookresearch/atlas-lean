# Truncation error for the exponential Burgers solution

Suppose `∑ i ∈ s, c i ≠ 0`, and let geometric majorants `m0`, `m1`, `mi`,
`mu` majorize the heat moment series of orders `0` and `1`, the inverse of
the order-`0` series, and `exponentialBurgersSeries s c k ν`. Let `r : Fin 2
→ ℚ≥0` be strictly smaller than all their radii, and let `x ∈ ℝ²` with `|x
i| ≤ r i`. Then for every `N : Fin 2 → ℕ`, the difference between the
classical solution `u(x 0, x 1)` and the rectangular partial sum of
`exponentialBurgersSeries s c k ν` over exponents `α` with `α i < N i` is at
most `M_u (∑ i, q_i ^ N_i) ∏ i, (1 - q_i)⁻¹`, where `M_u` is the bound of
`mu` and `q_i = r_i / (radius of mu)_i`.

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
