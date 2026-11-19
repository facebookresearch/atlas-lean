# Wired per-edge ambient tilted log normalizer

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices, and let $q, t \in \mathbb{R}$. The wired per-edge ambient tilted log-normalizer is

$$F^w_{G,\partial,q}(t) = \frac{1}{|E|} \log Z^w_{G,\partial}(\sigma(t), q) + \log(1 + e^t),$$

where $\sigma(s) = e^s/(1 + e^s)$ is the [logistic function](fsc-logistic.md), $Z^w_{G,\partial}(p, q) = \sum_\omega p^{o(\omega)} (1 - p)^{c(\omega)} q^{k^w(\omega)}$ is the [wired partition function](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-z.md) (the sum over all assignments $\omega$ of open/closed states to the unordered pairs of vertices, with $o(\omega)$ and $c(\omega)$ the numbers of open and closed edges of $G$ and $k^w(\omega)$ is the number of connected components of the graph whose edges are the open edges of $G$ together with all pairs of distinct vertices of $\partial$), $1/|E|$ is read as $0$ when $G$ has no edges, and $\log x$ means $\log |x|$ for $x \ne 0$ and $\log 0 = 0$.
