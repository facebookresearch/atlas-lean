# Average edge density of the $q = 2$ random-cluster measure

Let $G = (V, E)$ be a finite simple graph and $t \in \mathbb{R}$. The average edge density of $G$ at $t$ is

$$\rho_G(t) = \frac{1}{|E|} \sum_\omega \phi_{G,\sigma(t),2}(\omega)\, o(\omega),$$

the expected number of open edges of $G$ under the [random-cluster probability](../random-cluster-measures-on-finite-graphs/fk-prob.md) $\phi_{G,p,2}$ at $q = 2$ and $p = \sigma(t) = e^t/(1 + e^t)$, divided by $|E|$. The sum runs over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, $o(\omega)$ is the [number of open edges](../random-cluster-measures-on-finite-graphs/open-count.md) of $G$, and $1/|E|$ is read as $0$ when $G$ has no edges.
