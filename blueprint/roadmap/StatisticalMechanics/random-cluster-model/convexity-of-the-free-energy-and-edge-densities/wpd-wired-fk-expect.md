# Expectation under the wired FK measure

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, let $p, q \in \mathbb{R}$, and let $X$ be a real function of configurations. The wired expectation of $X$ is

$$\mathbb{E}^w_{G,\partial,p,q}[X] = \sum_\omega \phi^w_{G,\partial,p,q}(\omega)\, X(\omega),$$

the sum running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, where $\phi^w_{G,\partial,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k^w(\omega)} / Z^w_{G,\partial}(p, q)$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md); here $o(\omega)$ and $c(\omega)$ are the numbers of open and closed edges of $G$, $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$, and $Z^w_{G,\partial}(p, q)$ is the [wired partition function](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-z.md), the sum of the numerators over all $\omega$ (the quotient is read as $0$ if this sum is $0$). For $0 \le p \le 1$ and $q > 0$ (with $Z^w > 0$) this is the expectation of $X$ under a probability measure; for other real $p, q$ it is the normalized weighted sum above.
