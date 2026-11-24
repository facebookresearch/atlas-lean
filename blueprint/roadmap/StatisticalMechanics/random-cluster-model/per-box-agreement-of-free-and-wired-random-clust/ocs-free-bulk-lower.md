# Lower bound on free bulk edge marginals

Let $d, N, n \in \mathbb{N}$ with $n \ge 1$, $e'$ an unordered pair of vertices of $\Lambda_N$, $t \in \mathbb{R}$, and $u, v$ adjacent vertices of $\Lambda_{n - \lfloor\sqrt n\rfloor}$. Then

$$\theta^0_{e'}(\sigma(t)) - \Delta^0_n \le \phi_n(\{u, v\} \text{ open}),$$

where $\theta^0_e(p)$ is the [free edge density](free-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the free infinite-volume random-cluster measure on $\mathbb{Z}^d$, a chosen subsequential weak limit of the free box measures), $\Delta^0_n = \sum_{j, \pm} |\theta^0_{e'}(\sigma(t)) - m_n(j, \pm)|$ is the [free deviation](ocs-free-delta.md) with $m_n(j, \pm)$ is the [free unit-edge marginal](ocs-unit-marg.md) (for $R = \lfloor\sqrt n\rfloor \ge 1$, the probability that the unit edge $\{0, \pm e_j\}$ is open under the random-cluster measure on $\Lambda_R$ at $(\sigma(t), 2)$; $0$ when $R = 0$), $\phi_n = \phi_{\Lambda_n,\sigma(t),2}$ is the [random-cluster probability](../random-cluster-measures-on-finite-graphs/fk-prob.md) of the nearest-neighbour graph on $\Lambda_n = \{-n, \dots, n\}^d$, and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
