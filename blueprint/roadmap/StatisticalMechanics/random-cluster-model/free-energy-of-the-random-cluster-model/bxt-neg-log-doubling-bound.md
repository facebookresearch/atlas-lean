# Doubling bound at the dyadic scales $2^j$

Let $d \in \mathbb{N}$ and $t \in \mathbb{R}$. The dyadic doubling bound holds at $t$ when there is a sequence $(I_j)$ of nonnegative reals such that $\sum_j I_j / E(2^{j+1})$ converges (a term with zero denominator is read as $0$), and for every $j$

$$u_t(2^{j+1}) \le 2^d\, u_t(2^j) + I_j\, \big(-\log(1 - \sigma(t))\big) \quad\text{and}\quad \big|2^d E(2^j) - E(2^{j+1})\big| \le I_j,$$

where $u_t(n) = -\log Z_{\Lambda_n}(\sigma(t), 2)$ is the [negative log ambient normalizer](bxt-ambient-neg-log-z.md) of $\Lambda_n = \{-n, \dots, n\}^d$, $E(n)$ the [number of edges](bxt-e.md) of $\Lambda_n$, and $\sigma(t) = e^t/(1 + e^t)$.
