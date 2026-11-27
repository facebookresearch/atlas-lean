# Wired partition function at logistic $p$ as a tilted sum

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, and let $t, q \in \mathbb{R}$. Then

$$Z^w_{G,\partial}(\sigma(t), q) = \frac{\sum_\omega q^{k^w(\omega)}\, e^{t\, o(\omega)}}{(1 + e^t)^{|E|}},$$

where $Z^w_{G,\partial}$ is the [wired partition function](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-z.md), $\sigma(s) = e^s/(1 + e^s)$ is the [logistic function](fsc-logistic.md), the sum runs over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, $o(\omega)$ is the number of open edges of $G$, and $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$.
