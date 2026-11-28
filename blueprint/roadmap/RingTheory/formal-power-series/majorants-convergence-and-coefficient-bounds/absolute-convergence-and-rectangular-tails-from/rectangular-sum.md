# Rectangular partial sum of a power series

For truncation orders `N : Fin d → ℕ`, a rational power series `a` in `d`
variables and a real point `x ∈ ℝ^d`, `rectangularSum N a x` is the finite
sum of `coeff α a · ∏ i, x i ^ α i` over all exponents `α` with `α i < N i`
for every `i`.
