# Random-cluster connection probability

Let $G = (V, E)$ be a finite simple graph, $p, q \in \mathbb{R}$ and $x, y \in V$. The connection probability is

$$\phi_{G,p,q}(x \leftrightarrow y) = \sum_{\omega :\ x \leftrightarrow y} \phi_{G,p,q}(\omega),$$

where $x \leftrightarrow y$ means that $x$ and $y$ are [joined by a path](connected.md) of edges of $G$ open in $\omega$ (every vertex is joined to itself), and $\phi_{G,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)} / Z_G(p, q)$ is the [random-cluster probability](../../random-cluster-measures-on-finite-graphs/fk-prob.md) on assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), with $o(\omega)$ and $c(\omega)$ the numbers of open and closed edges of $G$, $k(\omega)$ the number of open clusters, and $Z_G(p, q)$ the sum of the numerators over all $\omega$ (the quotient is read as $0$ when $Z_G(p, q) = 0$). For $0 \le p \le 1$ and $q > 0$ the weights define a probability measure and the value lies in $[0, 1]$; for other real $p, q$ it is the normalized weighted sum above and need not be a probability.
