# Boundary values of the formal solution

For every exponent `n : σ →₀ ℕ` with `n i = 0`, the coefficient of `solution
i F boundary` at `n` equals the coefficient of `boundary` at `n`: the whole
slice `X_i`-degree `0`, not only the constant coefficient, comes from the
boundary series.

Here `K` is a field, `σ` an index set of variables and `i : σ` the selected
axis. A map `F` on formal power series is causal on axis `i` when, for every
`k`, series agreeing through degree `k` on axis `i` (coefficients equal at
every exponent `n` with `n i ≤ k`) have images agreeing through degree `k`
on axis `i`. The Picard iterates are `approx 0 = boundary` and `approx (n +
1) = pIntegral i (F (approx n)) boundary`, and `solution i F boundary` takes
its coefficient at `n` from the iterate `approx (n i)`.
