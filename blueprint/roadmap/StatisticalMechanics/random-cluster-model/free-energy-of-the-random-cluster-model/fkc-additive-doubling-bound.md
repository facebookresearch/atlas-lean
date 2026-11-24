# Doubling-bound property of the box free energy along $K_j$

Let $d \in \mathbb{N}$ and $s, q \in \mathbb{R}$. The doubling bound along $K_j$ holds when there is a sequence $(I_j)$ of nonnegative reals such that $\sum_j I_j / E(K_{j+1})$ converges (a term with zero denominator is read as $0$), and for every $j$

$$u(K_{j+1}) \le 2^d\, u(K_j) + I_j\, \big(-\log(1 - \sigma(s))\big) \quad\text{and}\quad \big|2^d E(K_j) - E(K_{j+1})\big| \le I_j,$$

where $u(n) = -\log Z^E_{\Lambda_n}(\sigma(s), q)$ is the [box free energy](fkc-u.md), $E(n)$ the [number of edges](agl-e.md) of $\Lambda_n = \{-n, \dots, n\}^d$, $K_j = 2^{j+1} - 1$ are the [scales](agl-k.md), and $\sigma(s) = e^s/(1 + e^s)$.
