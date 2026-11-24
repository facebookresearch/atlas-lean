# Edwards–Sokal spin marginal is the Potts measure

Let $G = (V, E)$ be a finite simple graph, $q \ge 1$ an integer, $\beta, J \in \mathbb{R}$, and $p = 1 - e^{-\beta J}$. For every coloring $\sigma : V \to \{0, \dots, q - 1\}$,

$$\frac{1}{Z^{ES}_q(p)} \sum_\omega W_p(\sigma, \omega) = \mu_{G,q,\beta,J}(\sigma),$$

where the left side is the [spin marginal](es-first-marginal.md) of the Edwards–Sokal measure ($W_p$ the [Edwards–Sokal weight](es-weight.md), $Z^{ES}_q(p)$ the [partition function](es-z.md), the sum over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included)) and $\mu_{G,q,\beta,J}$ is the [Potts probability](../the-q-state-potts-model-on-a-finite-graph/potts-prob.md) $\mu_{G,q,\beta,J}(\sigma) = e^{\beta J a(\sigma)} / \sum_{\sigma'} e^{\beta J a(\sigma')}$, with $a(\sigma)$ the number of edges of $G$ whose endpoints have the same color.
