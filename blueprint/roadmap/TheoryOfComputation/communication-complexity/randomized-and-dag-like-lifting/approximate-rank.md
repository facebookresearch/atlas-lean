# Approximate rank and the log-approximate-rank conjecture

For a sign matrix $F \in \{\pm 1\}^{X \times Y}$ and $0 \le \varepsilon < 1$, the **$\varepsilon$-approximate rank** is

$$
\operatorname{rank}_{\varepsilon}(F) = \min\bigl\{ \operatorname{rank}(M) : M \in \mathbb{R}^{X \times Y},\ |M(x,y) - F(x,y)| \le \varepsilon \ \forall x, y \bigr\}.
$$

Let $F = (-1)^{f}$ for $f : X \times Y \to \{0,1\}$. A private-coin protocol of cost $c$ whose private error probability for $f$ is at most $\varepsilon < 1/2$ at every input pair gives $\operatorname{rank}_{2\varepsilon}(F) \le 2^{c}$: the matrix $M(x,y)$ of expected values of $(-1)^{\text{output}}$ is a sum, over the at most $2^{c}$ leaves, of rank-one matrices, and $|M(x,y) - F(x,y)|$ is twice the error probability at $(x,y)$. Combined with Newman's theorem, for $X = Y = \{0,1\}^n$ and $0 < \varepsilon < 1/4$ the public-coin randomized communication complexity satisfies $R^{cc}_{\varepsilon}(f) \ge \log_2 \operatorname{rank}_{4\varepsilon}(F) - \log_2(n/\varepsilon^2) - C_0$, where $C_0$ is the constant of Newman's theorem. The **log-approximate-rank conjecture** (Lee-Shraibman) asserted a converse up to polynomial loss: $R^{cc}_{1/3}(f) \le \operatorname{poly}(\log \operatorname{rank}_{1/3}(F))$.

## Depends on

- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)
- [Error probability of a private-coin protocol](../randomized-communication-protocols/private-error-prob.md)
- [Newman's theorem](../randomized-communication-protocols/newman-private-coins.md)

## Sources

- T. Lee, A. Shraibman, "Lower bounds in communication complexity", Foundations and Trends in Theoretical Computer Science 3 (2009).
- I. Newman, "Private vs. common random bits in communication complexity", Information Processing Letters 39 (1991) 67-71.
- A. Chattopadhyay, N. S. Mande, S. Sherif, "The log-approximate-rank conjecture is false", STOC (2019); Journal of the ACM 67 (2020).
