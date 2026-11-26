# Dictatorship tests and their completeness and soundness

A **dictatorship test** for $\mathrm{GCSP}(\Lambda)$ on functions $F : [q]^R \to \Delta_q$ (the simplex of distributions on labels) is a distribution $\mathcal{T}$ over constraints $(P, (z^{(1)}, \dots, z^{(k)}))$ with $z^{(i)} \in [q]^R$; its value on $F$ is $\mathcal{T}(F) = \mathbb{E}\,\mathbb{E}_{a_i \sim F(z^{(i)})} P(a_1, \dots, a_k)$. Its **completeness** is $\min_{j \in [R]} \mathcal{T}(\mathrm{dict}_j)$ where $\mathrm{dict}_j(z) = z_j$. Its **$(\tau, d)$-soundness** is $\sup \mathcal{T}(F)$ over $F$ all of whose coordinates have degree-$d$ influence at most $\tau$:

$$
\max_{j \in [R]} \operatorname{Inf}_j^{\le d}(F) \le \tau.
$$

## Depends on

- [Generalized constraint satisfaction problems with payoff functions](generalized-csp.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- S. Khot, G. Kindler, E. Mossel, R. O'Donnell, "Optimal inapproximability results for MAX-CUT and other 2-variable CSPs?", SIAM Journal on Computing 37 (2007) 319-357.
- P. Raghavendra, "Optimal algorithms and inapproximability results for every CSP?", STOC (2008).
