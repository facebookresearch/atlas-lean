# Van Hove tiling bound for the edge partition function

For $d, m, n \in \mathbb{N}$ and $t \in \mathbb{R}$,

$$u(n) \le T^d\, u(m) - \big(E(n) - T^d E(m)\big) \log(1 - \sigma(t)),$$

where $T = \lfloor (2n+1)/(2m+1) \rfloor$ is the [number of cells per side](ecz-t.md), $u(n) = -\log Z^{e}_{\Lambda_n}(\sigma(t), 2)$ is the [negative log edge partition function](ecz-u.md) of the box $\Lambda_n = \{-n, \dots, n\}^d$ with its nearest-neighbour graph (and likewise $u(m)$), $E(n)$ is the number of edges of the nearest-neighbour graph on $\Lambda_n = \{-n, \dots, n\}^d$, and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
