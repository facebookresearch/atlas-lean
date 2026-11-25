# Ambient tilted log normalizer of a finite graph

Let $G = (V, E)$ be a finite simple graph and $q, t \in \mathbb{R}$. The ambient tilted log-normalizer is

$$F_{G,q}(t) = \frac{1}{|E|} \log Z_G(\sigma(t), q) + \log(1 + e^t),$$

where $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](fsc-logistic.md) and $Z_G(p, q)$ is the [ambient random-cluster normalizer](../random-cluster-measures-on-finite-graphs/fk-z.md) $Z_G(p, q) = \sum_\omega p^{o(\omega)} (1 - p)^{c(\omega)} q^{k(\omega)}$, the sum running over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), with $o(\omega)$ and $c(\omega)$ the numbers of open and closed edges of $G$ and $k(\omega)$ the number of open clusters (isolated vertices included). Here $1/|E|$ is read as $0$ when $G$ has no edges (then $F_{G,q}(t) = \log(1 + e^t)$), and $\log x$ means $\log |x|$ for $x \ne 0$ and $\log 0 = 0$ (for $q > 0$ the normalizer is positive).
