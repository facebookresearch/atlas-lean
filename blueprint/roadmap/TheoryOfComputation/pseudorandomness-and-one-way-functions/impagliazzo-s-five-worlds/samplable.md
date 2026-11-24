# Samplable distributions

Let $p$ be a polynomial with natural-number coefficients and let
$S$ be a family of maps $S_n$ from $p(n)$-bit coin strings to bitstrings. The pair $(p, S)$ is
samplable when every $S_n(r)$ has length exactly $n$ and some polynomial-time computable function
on bitstrings maps the canonical bitstring encoding of every pair $(n, r)$ to $S_n(r)$.

The distribution sampled at length $n$ is that of $S_n(r)$ for a uniformly random coin string
$r$. The sampler is a single uniform polynomial-time algorithm: per-length circuits would admit
noncomputable $\mathsf{P/poly}$ samplers. The coin count is a polynomial rather than $n$: a
distribution giving probability $2^{-(n+1)}$ to one output is samplable with $n + 1$ coins but
not from $n$ uniform coins.
