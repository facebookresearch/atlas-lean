# Free-energy data give $q = 2$ box uniqueness off countably many $t$

Let $d, N \in \mathbb{N}$ and suppose the [homogeneous free-energy data](fuc-homogeneous-free-energy-data.md) hold on $\Lambda_N = \{-N, \dots, N\}^d$: there is a convex $g : \mathbb{R} \to \mathbb{R}$ with $\theta^1_{e'}(\sigma(t)) = g'_+(t)$ and $\theta^0_{e'}(\sigma(t)) = g'_-(t)$ for every edge $e'$ of $\Lambda_N$ and every $t \in \mathbb{R}$. Then the set of $t$ for which some increasing set $A$ of configurations of $\Lambda_N$ has $\mu^0_t(A) \ne \mu^1_t(A)$ is countable. Here $\theta^0_e(p)$ is the [free edge density](free-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the free infinite-volume random-cluster measure on $\mathbb{Z}^d$, a chosen subsequential weak limit of the free box measures), $\theta^1_e(p)$ is the [wired edge density](wired-edge-density.md) of $e$ at $q = 2$ (the probability that $e$ is open under the wired infinite-volume random-cluster measure on $\mathbb{Z}^d$), $g'_-$ and $g'_+$ are the [left](../convexity-of-the-free-energy-and-edge-densities/pressure-left-deriv.md) and [right derivatives](../convexity-of-the-free-energy-and-edge-densities/pressure-right-deriv.md) (each read as $0$ where the one-sided derivative does not exist), $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md), and $\mu^0_t$ and $\mu^1_t$ are the [free](fuc-free-mass.md) and [wired mass functions](fuc-wired-mass.md) on configurations of $\Lambda_N$ (the probability, under the free, resp. wired, infinite-volume random-cluster measure on $\mathbb{Z}^d$ at $p = \sigma(t)$ and $q = 2$, that the restriction to the pairs of vertices of $\Lambda_N$ equals the given configuration), and $\mu(A) = \sum_{\omega \in A} \mu(\omega)$.

## Depends on

- [Homogeneous free-energy data on a box at $q = 2$](fuc-homogeneous-free-energy-data.md)
- [Free infinite-volume edge density](free-edge-density.md)
- [Wired infinite-volume edge density](wired-edge-density.md)
- [Left derivative of the pressure](../convexity-of-the-free-energy-and-edge-densities/pressure-left-deriv.md)
- [Right derivative of the pressure](../convexity-of-the-free-energy-and-edge-densities/pressure-right-deriv.md)
- [Logistic function $e^t/(1+e^t)$](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md)
- [Free $q = 2$ infinite-volume mass function on a box](fuc-free-mass.md)
- [Wired $q = 2$ infinite-volume mass function on a box](fuc-wired-mass.md)
- [Mass of an event under a mass function](../fkg-inequality-and-monotonicity-of-random-cluste/event-mass-prob.md)
- [Vertices of the box $\{-n, \dots, n\}^d$](../infinite-volume-random-cluster-measures/finite-and-infinite-volume-fk-measures-on-d/box-verts.md)
- [Increasing event](../../../Probability/correlation-inequalities/harris-fkg-bk/increasing-events-and-the-fkg-lattice-condition/is-increasing.md)
- [Configuration space of a statistical-mechanics model](../../../Probability/random-fields/spin-and-bond-configuration-spaces/config-space.md)
