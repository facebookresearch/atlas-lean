# Keyed function families in P/poly

Let $F = (F_n)_{n \in \mathbb{N}}$ be a keyed family of
Boolean functions: $F_n(k, x)$ is a Boolean value for every key $k \in \{0,1\}^{n^2}$ and every
input $x \in \{0,1\}^n$. Then $F$ is in P/poly when there is a polynomial $p$ with natural-number
coefficients such that for every $n$ some circuit, given as a list of at most $p(n)$ encoded
gates, computes $F_n$: for all $k$ and $x$, the evaluation of the circuit on the bitstring $kx$ of
length $n^2 + n$ (the bits of $k$ followed by the bits of $x$) has last gate value $F_n(k, x)$.
