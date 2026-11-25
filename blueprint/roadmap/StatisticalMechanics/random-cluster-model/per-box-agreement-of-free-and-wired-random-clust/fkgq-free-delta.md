# Total deviation of free unit-edge marginals from a free density

For $d, N, n \in \mathbb{N}$, an unordered pair $e$ of vertices of $\Lambda_N = \{-N, \dots, N\}^d$ (viewed as a pair of sites of $\mathbb{Z}^d$), and $q, t \in \mathbb{R}$, the free deviation is

$$\sum_{j = 1}^{d} \sum_{\pm} \big|\theta^0_{e,q}(\sigma(t)) - m_n(j, \pm)\big|,$$

where $\theta^0_{e,q}(p)$ is the [free edge density](free-edge-density.md) of $e$ at cluster weight $q$, $m_n(j, \pm)$ is the [free unit-edge marginal](fkgq-unit-marg.md) (for $R = \lfloor\sqrt n\rfloor \ge 1$, the probability that the unit edge $\{0, \pm e_j\}$ of $\Lambda_R$ is open under the random-cluster measure on $\Lambda_R$ at $(\sigma(t), q)$; $0$ when $R = 0$), and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
