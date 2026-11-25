# Total deviation of wired unit-edge marginals from a wired density

For $d, N, n \in \mathbb{N}$, an unordered pair $e$ of vertices of $\Lambda_N = \{-N, \dots, N\}^d$ (viewed as a pair of sites of $\mathbb{Z}^d$), and $q, t \in \mathbb{R}$, the wired deviation is

$$\sum_{j = 1}^{d} \sum_{\pm} \big|m^w_n(j, \pm) - \theta^1_{e,q}(\sigma(t))\big|,$$

where $\theta^1_{e,q}(p)$ is the [wired edge density](wired-edge-density.md) of $e$ at cluster weight $q$, $m^w_n(j, \pm)$ is the [wired unit-edge marginal](fkgq-unit-wired-marg.md) (for $R = \lfloor\sqrt n\rfloor \ge 1$, the probability that the unit edge $\{0, \pm e_j\}$ of $\Lambda_R$ is open under the wired random-cluster measure on $\Lambda_R$ with boundary $\partial\Lambda_R$ at $(\sigma(t), q)$; $0$ when $R = 0$), and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
