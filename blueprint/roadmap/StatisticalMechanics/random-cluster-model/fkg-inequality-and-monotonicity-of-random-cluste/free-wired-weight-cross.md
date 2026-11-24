# Holley's condition for free and wired weights when $q \ge 1$

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, $0 < p < 1$ and $q \ge 1$. For all assignments $a, b$ of open/closed states to the unordered pairs of vertices (loops and non-edges included),

$$w(a)\, w^w(b) \le w(a \wedge b)\, w^w(a \vee b),$$

where $w(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)}$ is the [random-cluster weight](../random-cluster-measures-on-finite-graphs/fk-weight.md) and $w^w(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k^w(\omega)}$ the [wired weight](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-weight.md); $o(\omega)$ and $c(\omega)$ count the open and closed edges of $G$, $k(\omega)$ is the number of open clusters, and $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$. Configurations are ordered coordinatewise (closed $<$ open), and $a \wedge b$, $a \vee b$ denote the coordinatewise minimum and maximum.
