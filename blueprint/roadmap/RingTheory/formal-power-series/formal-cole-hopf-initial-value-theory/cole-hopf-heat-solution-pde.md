# The Cole–Hopf transform of the heat solution solves Burgers

Let `K` have characteristic zero and let `b` have nonzero constant
coefficient. Then `u = coleHopf ν x (heatSolution ν t x b)` satisfies the
formal Burgers equation `∂u/∂X_t = ν ∂²u/∂X_x² - u ∂u/∂X_x`.

Here `K` is a field, `t` (time) and `x` (space) are distinct variables in
`σ`, the heat operator is `heatRhs ν x φ = ν ∂²φ/∂X_x²`, the Burgers
operator is `burgersRhs ν x u = ν ∂²u/∂X_x² - u ∂u/∂X_x`, and `coleHopf ν x
φ = -2ν (∂φ/∂X_x) φ⁻¹`. `heatSolution ν t x b` is the formal solution of
`∂φ/∂X_t = heatRhs ν x φ` whose coefficients at exponents with `n t = 0` are
those of `b`.
