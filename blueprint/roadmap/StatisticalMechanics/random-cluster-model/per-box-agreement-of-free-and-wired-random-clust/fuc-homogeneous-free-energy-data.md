# Homogeneous free-energy data on a box at $q = 2$

For $d, N \in \mathbb{N}$, the homogeneous free-energy data hold when there is a convex $g : \mathbb{R} \to \mathbb{R}$ such that for every edge $e'$ of $\Lambda_N = \{-N, \dots, N\}^d$ and every $t \in \mathbb{R}$,

$$\theta^1_{e'}(\sigma(t)) = g'_+(t) \quad\text{and}\quad \theta^0_{e'}(\sigma(t)) = g'_-(t),$$

where $\theta^0_e(p)$ is the [free edge density](free-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the free infinite-volume random-cluster measure on $\mathbb{Z}^d$, a chosen subsequential weak limit of the free box measures), $\theta^1_e(p)$ is the [wired edge density](wired-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the wired infinite-volume random-cluster measure on $\mathbb{Z}^d$), $g'_-$ and $g'_+$ are the [left](../convexity-of-the-free-energy-and-edge-densities/pressure-left-deriv.md) and [right derivatives](../convexity-of-the-free-energy-and-edge-densities/pressure-right-deriv.md) (each read as $0$ where the one-sided derivative does not exist), and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).

## Depends on

- [Free infinite-volume edge density](free-edge-density.md)
- [Wired infinite-volume edge density](wired-edge-density.md)
- [Logistic function $e^t/(1+e^t)$](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md)
- [Left derivative of the pressure](../convexity-of-the-free-energy-and-edge-densities/pressure-left-deriv.md)
- [Right derivative of the pressure](../convexity-of-the-free-energy-and-edge-densities/pressure-right-deriv.md)
- [Vertices of the box $\{-n, \dots, n\}^d$](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/box-verts.md)
- [Inclusion of box edges into $\mathbb{Z}^d$](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/edge-incl.md)
