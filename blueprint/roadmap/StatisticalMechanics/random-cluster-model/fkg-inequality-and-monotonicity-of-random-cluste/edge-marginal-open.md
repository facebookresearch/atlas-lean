# Probability that an edge is open under the random-cluster measure

Let $G = (V, E)$ be a finite simple graph, $p, q \in \mathbb{R}$, and $e$ an unordered pair of vertices. The probability that $e$ is open is

$$\phi_{G,p,q}(e \text{ open}) = \sum_{\omega :\ e \text{ open in } \omega} \phi_{G,p,q}(\omega),$$

where $\phi_{G,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k(\omega)} / Z_G(p, q)$ is the [random-cluster probability](../random-cluster-measures-on-finite-graphs/fk-prob.md) on assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), with $o(\omega)$ and $c(\omega)$ the numbers of open and closed edges of $G$, $k(\omega)$ the number of open clusters (isolated vertices included), and $Z_G(p, q)$ the sum of the numerators over all $\omega$ (a zero denominator gives $0$). For $0 \le p \le 1$ and $q > 0$ this is the probability that $e$ is open; for other parameters it is only a normalized signed sum, which can lie outside $[0, 1]$.
