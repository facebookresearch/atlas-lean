# Wired off-centre sandwich hypothesis

For $d, N \in \mathbb{N}$, the wired off-centre sandwich holds when for every edge $e'$ of $\Lambda_N = \{-N, \dots, N\}^d$ and every $t \in \mathbb{R}$, there are sets $I_n$ of edges of $\Lambda_n = \{-n, \dots, n\}^d$ and numbers $\delta_n \ge 0$ with $\delta_n \to 0$ such that every $e \in I_n$ satisfies $\theta^1_e(\sigma(t)) = \theta^1_{e'}(\sigma(t))$ and $\phi^w_n(e \text{ open}) \le \theta^1_{e'}(\sigma(t)) + \delta_n$, and $(E(n) - |I_n|)/E(n) \to 0$ (read as $0$ when $E(n) = 0$). Here $\sigma(t) = e^t/(1 + e^t)$, $E(n)$ is the number of edges of $\Lambda_n$, $\theta^0$ and $\theta^1$ are the [free](../per-box-agreement-of-free-and-wired-random-clust/free-edge-density.md) and [wired edge densities](../per-box-agreement-of-free-and-wired-random-clust/wired-edge-density.md) at $q = 2$, and $\phi_n(e \text{ open})$, $\phi^w_n(e \text{ open})$ are the edge marginals of the free and wired random-cluster probabilities on $\Lambda_n$ at $(\sigma(t), 2)$.

## Depends on

- [Logistic function $e^t/(1+e^t)$](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md)
- [Edge marginal of a mass function](../fkg-inequality-and-monotonicity-of-random-cluste/edge-marg-prob.md)
- [Vertex boundary of a box](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/box-boundary.md)
- [Nearest-neighbour graph on a box](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/box-graph.md)
- [Vertices of the box $\{-n, \dots, n\}^d$](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/box-verts.md)
- [Inclusion of box edges into $\mathbb{Z}^d$](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/edge-incl.md)
- [Wired random-cluster probability of a configuration](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md)
- [Wired infinite-volume edge density](../per-box-agreement-of-free-and-wired-random-clust/wired-edge-density.md)
