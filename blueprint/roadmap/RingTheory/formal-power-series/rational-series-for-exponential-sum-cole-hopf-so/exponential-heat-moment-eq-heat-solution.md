# The exponential heat profile is the formal heat solution

The heat moment series of order `0`, `∑ i ∈ s, c i exp(ν k_i ^ 2 t + k_i
x)`, equals the canonical formal solution of the heat equation `∂_t φ = ν
∂_x² φ` whose time-zero coefficients are those of `∑ i ∈ s, c i exp(k_i x)`.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`.
