# Existence and uniqueness for formal causal equations

Let `K` be a field of characteristic zero, `i : σ` a variable, and `F` a map
on multivariate formal power series over `K` that is causal on axis `i`. For
every series `b` there is a unique formal power series `u` with `∂u/∂X_i = F
u` whose coefficients at all exponents `n` with `n i = 0` equal those of
`b`. The solution is a formal power series and need not converge.

Here `K` is a field, `σ` an index set of variables and `i : σ` the selected
axis. A map `F` on formal power series is causal on axis `i` when, for every
`k`, series agreeing through degree `k` on axis `i` (coefficients equal at
every exponent `n` with `n i ≤ k`) have images agreeing through degree `k`
on axis `i`. The Picard iterates are `approx 0 = boundary` and `approx (n +
1) = pIntegral i (F (approx n)) boundary`, and `solution i F boundary` takes
its coefficient at `n` from the iterate `approx (n i)`.
