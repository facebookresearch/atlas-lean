# The value of a tensor in the laser method

Let $T = \sum_{i,j,k} a_{ijk}\, x_i y_j z_k$ be a tensor over variable sets $X, Y, Z$ and $\tau \in [2/3, 1]$. Its **rotation** $T^{r}$ is the tensor over $Y, Z, X$ in which the coefficient of $y_j z_k x_i$ is $a_{ijk}$, and $T^{rr}$ is the corresponding tensor over $Z, X, Y$. A tensor $T'$ over $X', Y', Z'$ is a **restriction** of $T$ if $T' = \sum_{i,j,k} a_{ijk}\, A(x_i) B(y_j) C(z_k)$ for linear maps $A, B, C$ from the spans of $X, Y, Z$ to the spans of $X', Y', Z'$; a **zeroing out** is the restriction to subsets $X' \subseteq X$, $Y' \subseteq Y$, $Z' \subseteq Z$ that sets all other variables to zero. Write $T^{\otimes N}$ for the $N$-th tensor power. The **$\tau$-value** of $T$ is

$$
V_\tau(T) = \sup\Bigl\{ \Bigl(\sum_{i=1}^{p} (n_i m_i k_i)^{\tau}\Bigr)^{1/(3N)} \Bigr\},
$$

the supremum taken over all $N \ge 1$, all $p$ and all direct sums $\bigoplus_{i=1}^{p}\langle n_i, m_i, k_i\rangle$ that are restrictions of $(T \otimes T^{r} \otimes T^{rr})^{\otimes N}$. The symmetrization $T \otimes T^{r} \otimes T^{rr}$ can increase the value of asymmetric tensors; the laser method bounds $V_\tau$ from below by zeroing outs, which are restrictions. By the asymptotic sum inequality, $V_{\omega/3}(T) \le \underline{R}(T)$ for every $T$, since $T^{r}$ and $T^{rr}$ have the same border rank as $T$.

## Depends on

- [Schönhage's asymptotic sum inequality](asymptotic-sum-inequality.md)

## Sources

- V. Strassen, "Relative bilinear complexity and matrix multiplication", Journal für die reine und angewandte Mathematik 375/376 (1987) 406-443.
- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
- J. Alman, V. Vassilevska Williams, "A refined laser method and faster matrix multiplication", SODA (2021), arXiv:2010.05846 (Sections 2.2 and 2.7).
