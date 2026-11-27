# Sum of an exponential heat moment series

For every order `n` and every real point `x ∈ ℝ²`, the sum `∑ α, coeff α · x
0 ^ α 0 · x 1 ^ α 1` of the heat moment series `exponentialHeatMoment s c k
ν n` equals the real heat moment `H_n(x 0, x 1) = ∑ i ∈ s, c i k_i ^ n exp(ν
k_i ^ 2 x 0 + k_i x 1)`.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`.
