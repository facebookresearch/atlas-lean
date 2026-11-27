# Cole–Hopf residual identity

Let `K` be a field, `ν ∈ K`, `t x : σ` variables, and `φ` a multivariate
formal power series over `K` with nonzero constant coefficient. Writing `u =
coleHopf ν x φ = -2ν (∂φ/∂X_x) φ⁻¹`, the Burgers residual of `u` is
expressed through the heat residual of `φ`:

`∂u/∂X_t + u ∂u/∂X_x - ν ∂²u/∂X_x² = -2ν ∂/∂X_x (φ⁻¹ (∂φ/∂X_t - ν
∂²φ/∂X_x²))`.

No heat equation for `φ` is assumed. This is a formal power series version
of Lemma 3.1 of Gesztesy and Holden.
