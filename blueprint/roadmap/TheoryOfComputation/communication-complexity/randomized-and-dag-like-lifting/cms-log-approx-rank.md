# Chattopadhyay–Mande–Sherif: the log-approximate-rank conjecture is false

There is an explicit family of total Boolean functions $F_n : \{0,1\}^n \times \{0,1\}^n \to \{\pm 1\}$ whose sign matrices have small approximate rank, $\log \operatorname{rank}_{1/3}(F_n) = O(\log^{c} n)$ for an absolute constant $c$, while their randomized communication complexity is $R^{cc}_{1/3}(F_n) = \Omega(\sqrt{n})$. Hence randomized (and quantum) communication complexity is not bounded by a polynomial in the logarithm of approximate rank.

## Proof sketch

Compose the XOR function of a sink-finding query problem on tournaments with an XOR gadget: the outer query function has low approximate spectral norm (it is a sum of few characters with small coefficients), which bounds the approximate rank of the composed matrix, while its randomized query complexity is $\Omega(n)$; a lifting argument for XOR gadgets transfers the query lower bound to randomized communication.

## Depends on

- [Approximate rank and the log-approximate-rank conjecture](approximate-rank.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Proof depends on

- [Composed functions, gadgets and lifting theorems](composed-function-lifting.md)
- [Göös–Pitassi–Watson: query-to-communication lifting for BPP](gpw-bpp-lifting.md)

## Sources

- A. Chattopadhyay, N. S. Mande, S. Sherif, "The log-approximate-rank conjecture is false", STOC (2019); Journal of the ACM 67 (2020).
