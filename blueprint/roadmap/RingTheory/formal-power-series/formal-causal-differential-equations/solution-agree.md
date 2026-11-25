# Picard iterates agree with the solution

If `F` is causal on axis `i`, then for every `n` the Picard iterate `approx
i F boundary n` agrees with `solution i F boundary` through degree `n` on
axis `i`.

Here `K` is a field, `σ` an index set of variables and `i : σ` the selected
axis. A map `F` on formal power series is causal on axis `i` when, for every
`k`, series agreeing through degree `k` on axis `i` (coefficients equal at
every exponent `n` with `n i ≤ k`) have images agreeing through degree `k`
on axis `i`. The Picard iterates are `approx 0 = boundary` and `approx (n +
1) = pIntegral i (F (approx n)) boundary`, and `solution i F boundary` takes
its coefficient at `n` from the iterate `approx (n i)`.
