# Initial slice of the formal heat solution

For every exponent `n` with `n t = 0`, the coefficient of `heatSolution ν t
x b` at `n` equals the coefficient of `b` at `n`.

Here `K` is a field, `t` (time) and `x` (space) are variables in `σ`, the heat operator is `heatRhs ν x φ = ν ∂²φ/∂X_x²`, the Burgers
operator is `burgersRhs ν x u = ν ∂²u/∂X_x² - u ∂u/∂X_x`, and `coleHopf ν x
φ = -2ν (∂φ/∂X_x) φ⁻¹`. `heatSolution ν t x b` is the Picard construction along `t` for
`∂φ/∂X_t = heatRhs ν x φ` with the coefficients of `b` at exponents with
`n t = 0`; it solves that equation in characteristic zero when `t ≠ x`, but
the identity here needs neither assumption: it holds even when `t` and `x` are the same variable.
