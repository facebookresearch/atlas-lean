# Holley's condition for free and wired probabilities when $q \ge 1$

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, $0 < p < 1$ and $q \ge 1$. For all assignments $a, b$ of open/closed states to the unordered pairs of vertices (loops and non-edges included),

$$\phi_{G,p,q}(a)\, \phi^w_{G,\partial,p,q}(b) \le \phi_{G,p,q}(a \wedge b)\, \phi^w_{G,\partial,p,q}(a \vee b),$$

where $\phi_{G,p,q}$ is the [random-cluster probability](../random-cluster-measures-on-finite-graphs/fk-prob.md) and $\phi^w_{G,\partial,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k^w(\omega)} / Z^w$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md), where $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$ and $Z^w$ is the sum of the numerators over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included). Configurations are ordered coordinatewise (closed $<$ open), and $a \wedge b$, $a \vee b$ denote the coordinatewise minimum and maximum.
