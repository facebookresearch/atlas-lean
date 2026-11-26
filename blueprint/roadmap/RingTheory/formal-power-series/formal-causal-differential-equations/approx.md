# Picard iterates of a formal differential equation

For a field `K`, a variable `i : σ`, a map `F` on multivariate formal power
series over `K` and a boundary series `boundary`, the Picard iterates are
defined by `approx i F boundary 0 = boundary` and `approx i F boundary (n +
1) = pIntegral i (F (approx i F boundary n)) boundary`, where `pIntegral i f
b` is the formal integral of `f` along `X_i` whose coefficients at exponents
with `n i = 0` are those of `b`.
