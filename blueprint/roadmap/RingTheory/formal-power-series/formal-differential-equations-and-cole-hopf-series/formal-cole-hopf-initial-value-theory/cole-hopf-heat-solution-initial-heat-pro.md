# Solving Burgers by the Cole–Hopf method

Let `K` have characteristic zero, let `ν ≠ 0`, and let `v` be any formal
power series. Take the profile `initialHeatProfile ν x v` (the series `b`
with `∂b/∂X_x = -(2ν)⁻¹ v b` and all `x`-degree-zero coefficients equal to
those of `1`), solve the heat equation in `t` with it as boundary data, and
apply the Cole–Hopf transform. The result is the canonical formal solution
of the Burgers equation `∂u/∂X_t = burgersRhs ν x u` whose coefficients at
all exponents with `n t = 0` are those of `v`.

Here `K` is a field, `t` (time) and `x` (space) are distinct variables in
`σ`, the heat operator is `heatRhs ν x φ = ν ∂²φ/∂X_x²`, the Burgers
operator is `burgersRhs ν x u = ν ∂²u/∂X_x² - u ∂u/∂X_x`, and `coleHopf ν x
φ = -2ν (∂φ/∂X_x) φ⁻¹`. `heatSolution ν t x b` is the formal solution of
`∂φ/∂X_t = heatRhs ν x φ` whose coefficients at exponents with `n t = 0` are
those of `b`.
