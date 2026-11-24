# Per-edge free energy of a box in the tilt variable

For $d, n \in \mathbb{N}$ and $t \in \mathbb{R}$, the per-edge free energy is

$$F(n) = -\frac{u(n)}{E(n)} + \log(1 + e^t),$$

where $u(n) = -\log Z^{e}_{\Lambda_n}(\sigma(t), 2)$ is the [negative log edge partition function](ecz-u.md) of the box $\Lambda_n = \{-n, \dots, n\}^d$ with its nearest-neighbour graph, $E(n)$ is the number of edges of the nearest-neighbour graph on $\Lambda_n = \{-n, \dots, n\}^d$, and the quotient is read as $0$ when $E(n) = 0$.
