# Approximate rank and the log-approximate-rank conjecture

For a sign matrix $F \in \{\pm 1\}^{X \times Y}$ and $0 \le \varepsilon < 1$, the **$\varepsilon$-approximate rank** is

$$
\operatorname{rank}_{\varepsilon}(F) = \min\bigl\{ \operatorname{rank}(M) : M \in \mathbb{R}^{X \times Y},\ |M(x,y) - F(x,y)| \le \varepsilon \ \forall x, y \bigr\}.
$$

It satisfies $R^{cc}_{\varepsilon'}(F) \ge \Omega(\log \operatorname{rank}_{\varepsilon}(F))$ for suitable $\varepsilon, \varepsilon'$, and the same for quantum communication. The **log-approximate-rank conjecture** (Lee-Shraibman) asserted the converse up to polynomial loss: $R^{cc}_{1/3}(F) \le \operatorname{poly}(\log \operatorname{rank}_{1/3}(F))$.

## Depends on

- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)
- [Public-coin randomized protocol](../randomized-communication-protocols/public-coin-protocol.md)

## Sources

- T. Lee, A. Shraibman, "Lower bounds in communication complexity", Foundations and Trends in Theoretical Computer Science 3 (2009).
- A. Chattopadhyay, N. S. Mande, S. Sherif, "The log-approximate-rank conjecture is false", STOC (2019); Journal of the ACM 67 (2020).
