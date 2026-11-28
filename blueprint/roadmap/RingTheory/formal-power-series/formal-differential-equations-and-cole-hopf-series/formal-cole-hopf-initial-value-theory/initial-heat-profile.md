# Normalized inverse Cole–Hopf profile

For a field `K`, `ν ∈ K`, a spatial variable `x : σ` and a power series `v`,
`initialHeatProfile ν x v` is the Picard construction (its coefficient at `n` is read from the `(n x)`-th Picard iterate along `x`), along the axis `x`, for
the linear equation `∂b/∂X_x = -(2ν)⁻¹ v b` whose coefficients at all
exponents with `n x = 0` are those of `1` (with `0⁻¹ = 0`, so for `ν = 0`
the equation is `∂b/∂X_x = 0`). For `ν ≠ 0` it is the formal counterpart of
`exp(-∫ v dx / (2ν))`; other variables, including time, act as parameters,
and the profile need not solve the heat equation. It solves the displayed
equation in characteristic zero; in characteristic `p` it need not (over
`𝔽₃` with `ν = v = 1` the equation `b′ = b`, `b(0) = 1` has no solution).
