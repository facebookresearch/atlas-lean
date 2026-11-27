# The exponential Cole–Hopf series is the formal Burgers solution

If `∑ i ∈ s, c i ≠ 0`, then `exponentialBurgersSeries s c k ν` equals the
canonical formal solution of the Burgers equation `∂_t u = ν ∂_x² u - u ∂_x
u` whose time-zero coefficients are those of the Cole–Hopf transform of the
initial profile `∑ i ∈ s, c i exp(k_i x)`.

Here `s` is a finite index set, `c k : ι → ℚ` are amplitudes and
frequencies, `ν ∈ ℚ` is the viscosity, variable `0` is time `t` and variable
`1` is space `x`. The heat moment series is `exponentialHeatMoment s c k ν n
= ∑ i ∈ s, c i k_i ^ n exp(ν k_i ^ 2 t + k_i x)` (as a formal power series
with rational coefficients), and `exponentialBurgersSeries s c k ν =
coleHopf ν 1 (exponentialHeatMoment s c k ν 0) = -2ν (∂_x φ) φ⁻¹` with `φ`
the moment of order `0`.
