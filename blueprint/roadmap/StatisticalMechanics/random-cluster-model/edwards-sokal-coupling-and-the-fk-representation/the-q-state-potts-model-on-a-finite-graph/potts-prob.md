# Potts probability of a spin configuration

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$ and $\beta, J \in \mathbb{R}$. The Potts probability of a coloring $\sigma : V \to \{0, \dots, q - 1\}$ is

$$\mu_{G,q,\beta,J}(\sigma) = \frac{e^{\beta J a(\sigma)}}{Z_{G,q}(\beta, J)},$$

the [Potts weight](potts-weight.md) divided by the [partition function](potts-z.md) $Z_{G,q}(\beta, J) = \sum_{\sigma'} e^{\beta J a(\sigma')}$, with $a(\sigma)$ the [agreement count](agreement.md) (the quotient is read as $0$ when there is no coloring, i.e. $q = 0$ and $V \ne \emptyset$).
