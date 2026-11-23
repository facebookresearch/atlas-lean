# Convex free-energy hypothesis for a box edge at $q = 2$

Let $d, N \in \mathbb{N}$ and let $e$ be an unordered pair of vertices of the box $\Lambda_N = \{-N, \dots, N\}^d \subseteq \mathbb{Z}^d$ (not necessarily an edge), viewed as a pair of sites of $\mathbb{Z}^d$. The convex free-energy hypothesis for $e$ holds when there is a convex function $g : \mathbb{R} \to \mathbb{R}$ such that for every $t \in \mathbb{R}$

$$g'_+(t) = \theta^1_e(\sigma(t)) \quad\text{and}\quad g'_-(t) = \theta^0_e(\sigma(t)),$$

where $\sigma(t) = e^t/(1 + e^t)$, and $\theta^1_e$ and $\theta^0_e$ are the [wired](../per-box-agreement-of-free-and-wired-random-clust/wired-edge-density.md) and [free edge densities](../per-box-agreement-of-free-and-wired-random-clust/free-edge-density.md) of $e$ at $q = 2$ (the probabilities that $e$ is open under the wired and free infinite-volume random-cluster measures on $\mathbb{Z}^d$). Here $g'_+(t)$ and $g'_-(t)$ denote the [right](pressure-right-deriv.md) and [left derivatives](pressure-left-deriv.md) of $g$ at $t$, each read as $0$ when the one-sided limit does not exist.
