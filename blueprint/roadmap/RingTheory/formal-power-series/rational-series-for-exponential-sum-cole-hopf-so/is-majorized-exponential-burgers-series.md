# Majorant for the exponential Cole–Hopf series

Let `R : Fin 2 → ℚ`, and let geometric majorants `m1` and `mi`, both with
radii `R`, majorize the heat moment series of order `1` and the inverse of
the heat moment series of order `0`. Then `exponentialBurgersSeries s c k ν`
is majorized with bound `|-2ν| · M_1 · M_i` and radii `R i / 2`, where `M_1`
and `M_i` are the bounds of `m1` and `mi`.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`. A geometric majorant `m` with bound `M ≥ 0` and
radii `R_i > 0` majorizes a rational power series `a` when `|coeff α a| ≤ M
∏ i, R_i ^ (-α i)` for every exponent `α`.
