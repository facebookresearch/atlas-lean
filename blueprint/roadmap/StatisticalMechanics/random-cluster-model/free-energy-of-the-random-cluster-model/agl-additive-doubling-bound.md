# Additive doubling bound along the scales $K_j$

Let $d \in \mathbb{N}$ and $t \in \mathbb{R}$. The additive doubling bound along $K_j$ holds at $t$ when there is a sequence $(I_j)_{j \in \mathbb{N}}$ of nonnegative reals such that $\sum_j I_j / E(K_{j+1})$ converges (a term with zero denominator is read as $0$), and for every $j$

$$u_t(K_{j+1}) \le 2^d\, u_t(K_j) + I_j\, \big(-\log(1 - \sigma(t))\big) \quad\text{and}\quad \big|2^d E(K_j) - E(K_{j+1})\big| \le I_j,$$

where $K_j = 2^{j+1} - 1$ are the [scales](agl-k.md), $u_t(n) = -\log Z_{\Lambda_n}(\sigma(t), 2)$ is the [negative log ambient normalizer](agl-ambient-neg-log-z.md) of $\Lambda_n$, $E(n)$ is the [number of edges](agl-e.md) of $\Lambda_n$, and $\sigma(t) = e^t/(1 + e^t)$.
