# Comparison inequalities between random-cluster and Bernoulli measures

Let $G = (V, E)$ be a finite simple graph, $0 < p < 1$ and $q \ge 1$, and put $r = p/(p + q(1 - p))$, the [reduced density](reduced-density.md). Then

$$\phi_{G,r,1} \preceq \phi_{G,p,q} \preceq \phi_{G,p,1},$$

where $\phi_{G,p,q}$ is the [random-cluster probability](../random-cluster-measures-on-finite-graphs/fk-prob.md) on assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included), $\phi_{G,r,1}$ is the random-cluster probability at $q = 1$, which makes the edges of $G$ independent Bernoulli($r$) and the other unordered pairs of vertices independent fair bits, and $\mu \preceq \nu$ means $\mu(A) \le \nu(A)$ for every increasing set $A$ of configurations. Each function $\mu$ on configurations is viewed as the measure $\sum_\omega \max(\mu(\omega), 0)\, \delta_\omega$. On the states of the edges of $G$ this is the comparison of the random-cluster measure with Bernoulli percolation (Fortuin 1972; Grimmett, *The Random-Cluster Model*, 2006, Theorem 3.21).
