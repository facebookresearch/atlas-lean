# The hard-core model as a weighted CSP

A two-state spin system on a graph $G = (V, E)$ is given by a symmetric edge matrix $A = \begin{pmatrix} \beta & 1 \\ 1 & \gamma \end{pmatrix}$ with $\beta, \gamma \ge 0$ and a vertex vector $b = (\lambda, 1)$ with $\lambda > 0$; a configuration $\sigma : V \to \{0, 1\}$ has weight $w(\sigma) = \prod_{(u,v) \in E} A_{\sigma(u),\sigma(v)} \prod_{v \in V} b_{\sigma(v)}$, and the partition function is $Z(G) = \sum_\sigma w(\sigma)$. This is the weighted CSP over the domain $\{0,1\}$ with one binary constraint with weight table $A$ on each edge and one unary constraint with weight table $b$ on each vertex. The *hard-core model* with fugacity $\lambda$ is the case $\beta = 0$, $\gamma = 1$: an edge has weight $0$ when both endpoints are in state $0$ and $1$ otherwise, and a vertex has weight $\lambda$ in state $0$ and $1$ in state $1$.

## Proof sketch

(Derived.) A configuration is the indicator of the vertex set $I = \sigma^{-1}(0)$; the edge weights vanish unless $I$ is independent, and the vertex weights contribute $\lambda^{|I|}$, so $Z(G) = \sum_I \lambda^{|I|}$ over the independent sets $I$ of $G$, the independence polynomial evaluated at $\lambda$.

## Depends on

- [Partition function of a weighted CSP](partition-function-of-a-weighted-csp.md)

## Sources

- L. Li, P. Lu and Y. Yin, "Correlation Decay up to Uniqueness in Spin Systems", Proceedings of the 24th ACM-SIAM Symposium on Discrete Algorithms (SODA 2013), 2013; arXiv:1111.7064, Section 2 (definition of two-state spin systems; $\beta = 0$, $\gamma = 1$ is the hardcore model).
- Dror Weitz, "Counting Independent Sets up to the Tree Threshold", Proceedings of the 38th Annual ACM Symposium on Theory of Computing (STOC 2006), 2006 (the hard-core model and its partition function).
- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
