# Probabilistic polynomial time with unbounded error

The class PP consists of the decision
problems $L$ for which there are a polynomial $p$ with natural-number coefficients and a
polynomial-time computable function $R$ on pairs of bitstrings such that, for every bitstring $x$
and $r$ uniformly random among the bitstrings of length $p(|x|)$, the probability that $R(x, r)$
is true is greater than $1/2$ if $L(x)$ is true, and at most $1/2$ if $L(x)$ is false.
