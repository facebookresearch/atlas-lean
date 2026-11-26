# Average wired edge density as the mean of edge marginals

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, and let $q, t \in \mathbb{R}$. Then the [average wired edge density](wpd-avg-wired-density.md) is

$$\rho^w_{G,\partial,q}(t) = \frac{1}{|E|} \sum_{e \in E} \phi^w_{G,\partial,\sigma(t),q}(e \text{ open}),$$

where $1/|E|$ is read as $0$ when $G$ has no edges, $\sigma(s) = e^s/(1 + e^s)$ is the [logistic function](fsc-logistic.md) and $\phi^w_{G,\partial,p,q}$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) $\phi^w_{G,\partial,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k^w(\omega)} / Z^w_{G,\partial}(p, q)$ on assignments $\omega$ of open/closed states to all unordered pairs of vertices; here $o(\omega)$ and $c(\omega)$ are the numbers of open and closed edges of $G$, $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$, and $Z^w_{G,\partial}(p, q)$ is the [wired partition function](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-z.md), the sum of the numerators over all $\omega$ (the quotient is read as $0$ if this sum is $0$).
