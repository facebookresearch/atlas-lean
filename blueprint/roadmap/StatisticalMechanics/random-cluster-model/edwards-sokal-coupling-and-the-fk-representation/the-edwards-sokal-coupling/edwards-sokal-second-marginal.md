# Edwards–Sokal bond marginal is the random-cluster measure

Let $G = (V, E)$ be a finite simple graph, $q \in \mathbb{N}$, $\beta, J \in \mathbb{R}$, and $p = 1 - e^{-\beta J}$. For every assignment $\omega$ of open/closed states to the unordered pairs of vertices,

$$\frac{1}{Z^{ES}_q(p)} \sum_\sigma W_p(\sigma, \omega) = \phi_{G,p,q}(\omega),$$

where the left side is the [bond marginal](es-second-marginal.md) of the Edwards–Sokal measure ($W_p$ the [Edwards–Sokal weight](es-weight.md), $Z^{ES}_q(p)$ the [partition function](es-z.md), the sum over all colorings $\sigma : V \to \{0, \dots, q - 1\}$) and $\phi_{G,p,q}$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) $\phi_{G,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)} / Z_G(p, q)$ on assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), with $o(\omega)$ and $c(\omega)$ the numbers of open and closed edges of $G$, $k(\omega)$ the number of open clusters, and $Z_G(p, q)$ the sum of the numerators over all $\omega$.
