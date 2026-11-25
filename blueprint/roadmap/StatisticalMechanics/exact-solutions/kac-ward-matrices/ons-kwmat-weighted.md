# Edge-weighted Kac-Ward matrix

For $L \in \mathbb{N}$, a weight $w$ on unordered pairs of sites of the discrete torus $T_L = (\mathbb{Z}/L\mathbb{Z})^2$ ($L \in \mathbb{N}$, with $\mathbb{Z}/0\mathbb{Z} = \mathbb{Z}$), and $\omega \in \mathbb{C}$, the matrix is indexed by darts $(p, \mu)$ of $T_L$ (a site $p$ and a direction $\mu \in \{0, 1, 2, 3\}$): for $d_1 = (p_1, \mu_1)$ and $d_2 = (p_2, \mu_2)$,

$$K^w_\omega(d_2, d_1) = \begin{cases} w(\{p_1, p_1 + s(\mu_1)\})\, w_\omega(\mu_1, \mu_2) & \text{if } p_2 = p_1 + s(\mu_1), \\ 0 & \text{otherwise,} \end{cases}$$

where directions $0, 1, 2, 3$ have unit steps $s(0) = (1, 0)$, $s(1) = (0, 1)$, $s(2) = (-1, 0)$, $s(3) = (0, -1)$ and $w_\omega(\mu, \nu)$ is the [turn weight](ons-turn-w.md) ($1$ if $\nu = \mu$, $\omega$ if $\nu = \mu + 1$, $0$ if $\nu = \mu + 2$, $\omega^{-1}$ if $\nu = \mu + 3$, indices mod $4$).
