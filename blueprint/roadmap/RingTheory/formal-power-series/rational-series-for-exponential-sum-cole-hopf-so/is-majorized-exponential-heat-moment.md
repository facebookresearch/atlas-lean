# Majorant for an exponential heat moment series

Let `R : Fin 2 → ℚ` be positive radii with `|ν k_i ^ 2| ≤ 1 / R 0` and
`|k_i| ≤ 1 / R 1` for every `i ∈ s`. Then for every order `n`, the heat
moment series `exponentialHeatMoment s c k ν n` is majorized with bound `∑ i
∈ s, |c i k_i ^ n|` and radii `R`.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`. A geometric majorant `m` with bound `M ≥ 0` and
radii `R_i > 0` majorizes a rational power series `a` when `|coeff α a| ≤ M
∏ i, R_i ^ (-α i)` for every exponent `α`.
