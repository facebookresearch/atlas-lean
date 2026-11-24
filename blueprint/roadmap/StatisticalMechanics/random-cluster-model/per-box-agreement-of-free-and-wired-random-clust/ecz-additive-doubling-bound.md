# Additive doubling bound for the edge partition function

For $d \in \mathbb{N}$ and $t \in \mathbb{R}$, the additive doubling bound holds when there is a sequence $I_j \ge 0$ such that $\sum_j I_j / E(K_{j+1})$ converges and, for every $j \in \mathbb{N}$,

$$u(K_{j+1}) \le 2^d\, u(K_j) - I_j \log(1 - \sigma(t)) \quad\text{and}\quad |2^d E(K_j) - E(K_{j+1})| \le I_j,$$

where $K_j = 2^{j+1} - 1$ are the [dyadic scales](../free-energy-of-the-random-cluster-model/agl-k.md), $E(n)$ is the number of edges of the nearest-neighbour graph on $\Lambda_n = \{-n, \dots, n\}^d$ (as a real number, with $x/0 = 0$), $u(n) = -\log Z^{e}_{\Lambda_n}(\sigma(t), 2)$ is the [negative log edge partition function](ecz-u.md) of the box $\Lambda_n = \{-n, \dots, n\}^d$ with its nearest-neighbour graph, and $\sigma(t) = e^t/(1 + e^t)$ is the [logistic function](../convexity-of-the-free-energy-and-edge-densities/fsc-logistic.md).
