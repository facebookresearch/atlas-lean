# Upper bound on wired bulk edge marginals

Let $d, N, n \in \mathbb{N}$ with $n \ge 2$, $e'$ an unordered pair of vertices of $\Lambda_N$, $t \in \mathbb{R}$, and $u, v$ adjacent vertices of $\Lambda_{n - \lfloor\sqrt n\rfloor - 1}$. Then

$$\phi^w_n(\{u, v\} \text{ open}) \le \theta^1_{e'}(\sigma(t)) + \Delta^1_n,$$

where $\phi^w_n$ is the [wired random-cluster probability](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/wired-fk-prob.md) of $\Lambda_n = \{-n, \dots, n\}^d$ with boundary $\partial\Lambda_n = \Lambda_n \setminus \Lambda_{n-1}$ at $(\sigma(t), 2)$, $\theta^1_e(p)$ is the [wired edge density](wired-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the wired infinite-volume random-cluster measure on $\mathbb{Z}^d$), $\Delta^1_n = \sum_{j, \pm} |m^w_n(j, \pm) - \theta^1_{e'}(\sigma(t))|$ is the [wired deviation](ocs-wired-delta.md) with $m^w_n(j, \pm)$ is the [wired unit-edge marginal](ocs-unit-wired-marg.md) (for $R = \lfloor\sqrt n\rfloor \ge 1$, the probability that the unit edge $\{0, \pm e_j\}$ is open under the wired random-cluster measure on $\Lambda_R$ with boundary $\partial\Lambda_R$ at $(\sigma(t), 2)$; $0$ when $R = 0$), and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
