# Finite-volume tilt data for a box edge at $q = 2$

Let $d, N \in \mathbb{N}$ and let $e$ be an unordered pair of vertices of the box $\Lambda_N = \{-N, \dots, N\}^d \subseteq \mathbb{Z}^d$ (not necessarily an edge), viewed as a pair of sites of $\mathbb{Z}^d$. The finite-volume tilt data for $e$ hold when there are real sequences $(S_n)_{n \in \mathbb{N}}$ and $(V_n)_{n \in \mathbb{N}}$ with $V_n > 0$ for all $n$, $S_n/V_n \to 0$ and $V_n \to \infty$, such that for all $p, p' \in (0, 1)$ with $p' < p$ and every $\varepsilon > 0$ there is $n_0 \in \mathbb{N}$ with

$$\varepsilon \le \frac{2^{S_n}\, \lambda^{(\theta^1_e(p') - \theta^0_e(p) - 2\varepsilon) V_n}}{\varepsilon} \quad \text{for all } n \ge n_0, \qquad \lambda = \frac{p'(1 - p)}{(1 - p')\,p},$$

where $\lambda$ is the [tilt factor](../random-cluster-measures-on-finite-graphs/tilt-factor.md) and $\theta^1_e$, $\theta^0_e$ are the [wired](../per-box-agreement-of-free-and-wired-random-clust/wired-edge-density.md) and [free edge densities](../per-box-agreement-of-free-and-wired-random-clust/free-edge-density.md) of $e$ at $q = 2$: the probabilities that $e$ is open under the wired and free infinite-volume random-cluster measures on $\mathbb{Z}^d$ (chosen subsequential weak limits of the box measures).
