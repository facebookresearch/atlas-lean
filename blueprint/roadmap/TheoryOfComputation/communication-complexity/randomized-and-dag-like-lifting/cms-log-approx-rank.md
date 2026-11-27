# Chattopadhyay–Mande–Sherif: the log-approximate-rank conjecture is false

There is an explicit family of total Boolean functions $F_n : \{0,1\}^n \times \{0,1\}^n \to \{\pm 1\}$ whose sign matrices have small approximate rank, $\operatorname{rank}_{1/3}(F_n) = O(n^2)$, so $\log \operatorname{rank}_{1/3}(F_n) = O(\log n)$, while their randomized communication complexity is $R^{cc}_{1/3}(F_n) = \Omega(\sqrt{n})$. Hence randomized communication complexity is not bounded by a polynomial in the logarithm of approximate rank. The same family also refutes the quantum version of the conjecture: its quantum communication complexity is polynomial in $n$ (Anshu–Boddu–Touchette; Sinha–de Wolf, independently).

## Proof sketch

Take $F = \mathrm{SINK} \circ \mathrm{XOR}^n$, where $\mathrm{SINK}$ reads the $n = \binom{m}{2}$ edge orientations of a tournament on $m$ vertices and outputs whether the tournament has a sink. A tournament has at most one sink, so $\mathrm{SINK}$ is the sum over the $m$ vertices of the conjunction saying that the vertex is a sink; each conjunction has spectral norm $1$, so $\mathrm{SINK}$ has spectral norm at most $m = O(\sqrt{n})$, which bounds $\operatorname{rank}_{1/3}(F)$ by $O(n^2)$. The lower bound $R^{cc}_{1/3}(F) = \Omega(\sqrt{n})$ is proved by Chattopadhyay–Mande–Sherif for this composed function; it does not come from a general lifting theorem for the XOR gadget, since none holds ($\mathrm{PARITY}_n \circ \mathrm{XOR}^n$ has communication complexity $O(1)$ while $\mathrm{PARITY}_n$ has query complexity $n$), and $\mathrm{SINK}$ itself has deterministic query complexity $O(m) = O(\sqrt{n})$.

## Depends on

- [Approximate rank and the log-approximate-rank conjecture](approximate-rank.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Proof depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)

## Sources

- A. Chattopadhyay, N. S. Mande, S. Sherif, "The log-approximate-rank conjecture is false", STOC (2019); Journal of the ACM 67 (2020).
- A. Anshu, N. G. Boddu, D. Touchette, "Quantum log-approximate-rank conjecture is also false", FOCS (2019), arXiv:1811.10525.
- M. Sinha, R. de Wolf, "Exponential separation between quantum communication and logarithm of approximate rank", FOCS (2019), arXiv:1811.10090.
