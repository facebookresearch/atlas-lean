# Twisted Kac-Ward matrix with decorated transition weights

For $L \in \mathbb{N}$, a weight $\eta$ on decorated edges and $\omega, u, v \in \mathbb{C}$, the matrix is indexed by the darts: for $d_2 = (p_2, \mu_2)$ and $d_1 = (p_1, \mu_1)$,

$$K^{\mathrm{dec}}_\eta(d_2, d_1) = \begin{cases} \pi_{u,v}(\mu_1)\, \tau_\eta(d_2, d_1)\, w_\omega(\mu_1, \mu_2) & \text{if } p_2 = p_1 + s(\mu_1), \\ 0 & \text{otherwise,} \end{cases}$$

where $\tau_\eta$ is the [transition weight](ons-dec-transition-weight.md), $\pi_{u,v}$ is the [direction phase](../kac-ward-matrices/ons-dir-phase.md), and $w_\omega$ is the [turn weight](../kac-ward-matrices/ons-turn-w.md).
