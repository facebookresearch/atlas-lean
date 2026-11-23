# BPP

The class BPP of bounded-error probabilistic polynomial-time decision problems
consists of the decision problems $L$ for which there are a polynomial $p$ with natural number
coefficients and a polynomial-time computable function $R$ from pairs of bitstrings to booleans
such that, for every bitstring $x$, writing $m = p(|x|)$ and $c_x$ for the number of strings
$r \in \{0,1\}^m$ with $R(x, r)$ true: if $L(x)$ is true then $3 c_x \ge 2 \cdot 2^m$, and if
$L(x)$ is false then $3 c_x \le 2^m$. That is, for a uniformly random $r$, $R(x, r)$ is true with
probability at least $2/3$ on yes-instances and at most $1/3$ on no-instances.
