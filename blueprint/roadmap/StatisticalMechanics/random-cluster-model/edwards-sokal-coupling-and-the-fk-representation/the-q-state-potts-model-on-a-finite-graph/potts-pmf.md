# Potts Gibbs measure as a probability mass function

Let $G = (V, E)$ be a finite simple graph, $q \ge 1$ an integer and $\beta, J \in \mathbb{R}$. The Potts Gibbs measure is the probability measure on the colorings $\sigma : V \to \{0, \dots, q - 1\}$ that gives each $\sigma$ the mass $\mu_{G,q,\beta,J}(\sigma) = e^{\beta J a(\sigma)} / \sum_{\sigma'} e^{\beta J a(\sigma')}$, the [Potts probability](potts-prob.md), with $a(\sigma)$ the number of edges of $G$ whose endpoints have the same color.
