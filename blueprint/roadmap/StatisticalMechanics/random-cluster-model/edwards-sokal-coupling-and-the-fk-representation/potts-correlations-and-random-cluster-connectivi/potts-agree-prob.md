# Potts two-point agreement probability

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$, $\beta, J \in \mathbb{R}$ and $x, y \in V$. The two-point agreement probability is

$$\mu_{G,q,\beta,J}(\sigma_x = \sigma_y) = \sum_{\sigma :\ \sigma_x = \sigma_y} \mu_{G,q,\beta,J}(\sigma),$$

the sum over colorings $\sigma : V \to \{0, \dots, q - 1\}$ with $\sigma_x = \sigma_y$ of the [Potts probability](../the-q-state-potts-model-on-a-finite-graph/potts-prob.md) $\mu_{G,q,\beta,J}(\sigma) = e^{\beta J a(\sigma)} / \sum_{\sigma'} e^{\beta J a(\sigma')}$, with $a(\sigma)$ the number of edges of $G$ whose endpoints have the same color. For $q \ge 1$ this is a probability in $[0, 1]$, equal to $1$ when $x = y$. For $q = 0$ there are no colorings and the value is $0$, even when $x = y$ (unless $V$ is empty, in which case $x, y$ do not exist).
