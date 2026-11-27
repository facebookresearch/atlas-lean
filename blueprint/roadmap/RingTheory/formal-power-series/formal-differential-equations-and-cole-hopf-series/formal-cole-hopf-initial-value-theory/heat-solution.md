# Formal heat solution

For a field `K`, `ν ∈ K`, variables `t` and `x`, and a power series `b`,
`heatSolution ν t x b` is the Picard construction along `t` (its coefficient
at `n` is read from the `(n t)`-th Picard iterate) for the heat equation
`∂φ/∂X_t = ν ∂²φ/∂X_x²`, with the coefficients of `b` at all exponents with
`n t = 0`. In characteristic zero and with `t ≠ x`, it solves the heat equation and is the unique solution with that time-zero slice; without these assumptions it need not (for `t = x`, `ν = 1` and boundary `t²` the construction gives `2t`, whose first and second derivatives differ).
