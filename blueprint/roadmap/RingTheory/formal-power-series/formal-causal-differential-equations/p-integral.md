# Formal integration along one variable

For a field `K`, a variable `i : σ`, and multivariate formal power series
`f` and `b` over `K`, `pIntegral i f b` is the series whose coefficient at
an exponent `n` is the coefficient of `b` at `n` if `n i = 0`, and otherwise
the coefficient of `f` at `n` with the `i`-th exponent lowered by one,
divided by `n i` (in `K`, with the convention `x / 0 = 0`). Coefficients of
`b` with `n i > 0` do not enter.
