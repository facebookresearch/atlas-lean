# The formal heat solution solves the heat equation

Let `K` have characteristic zero and `t ≠ x`. For every `ν` and every power
series `b`, `φ = heatSolution ν t x b` satisfies `∂φ/∂X_t = ν ∂²φ/∂X_x²`.

Here `K` is a field, `t` (time) and `x` (space) are distinct variables in
`σ`, the heat operator is `heatRhs ν x φ = ν ∂²φ/∂X_x²`, the Burgers
operator is `burgersRhs ν x u = ν ∂²u/∂X_x² - u ∂u/∂X_x`, and `coleHopf ν x
φ = -2ν (∂φ/∂X_x) φ⁻¹`. `heatSolution ν t x b` is the formal solution of
`∂φ/∂X_t = heatRhs ν x φ` whose coefficients at exponents with `n t = 0` are
those of `b`.
