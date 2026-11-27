# Initial slice of the transformed heat solution

Let `b` have nonzero constant coefficient. For every exponent `n` with `n t
= 0`, the coefficient of `coleHopf ν x (heatSolution ν t x b)` at `n` equals
the coefficient of `coleHopf ν x b` at `n`: the whole time-zero slice is the
Cole–Hopf transform of the boundary data.

Here `K` is a field, `t` (time) and `x` (space) are distinct variables in
`σ`, the heat operator is `heatRhs ν x φ = ν ∂²φ/∂X_x²`, the Burgers
operator is `burgersRhs ν x u = ν ∂²u/∂X_x² - u ∂u/∂X_x`, and `coleHopf ν x
φ = -2ν (∂φ/∂X_x) φ⁻¹`. `heatSolution ν t x b` is the Picard construction along `t` for
`∂φ/∂X_t = heatRhs ν x φ` with the coefficients of `b` at exponents with
`n t = 0`; it solves that equation in characteristic zero when `t ≠ x`. The
transformed-slice identity needs distinct axes and a nonzero boundary constant coefficient, but not
characteristic zero.
