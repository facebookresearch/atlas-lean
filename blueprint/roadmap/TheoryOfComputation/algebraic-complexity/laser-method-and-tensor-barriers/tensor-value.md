# The value of a tensor in the laser method

Let $T$ be a tensor over $X \otimes Y \otimes Z$ and $\tau \in [2/3, 1]$. Write $T^{\otimes N}$ for its $N$-th tensor power. The **$\tau$-value** of $T$ is

$$
V_\tau(T) = \lim_{N \to \infty} \sup\Bigl\{ \Bigl(\sum_{i=1}^{p} (n_i m_i k_i)^{\tau}\Bigr)^{1/N} \Bigr\},
$$

the supremum taken over all $p$ and all direct sums $\bigoplus_{i=1}^{p}\langle n_i, m_i, k_i\rangle$ obtainable from $T^{\otimes N}$ by zeroing out variables (a restriction that sets some basis variables of $X, Y, Z$ to zero) or, more generally, by degenerations of polynomial cost. By the asymptotic sum inequality, $V_{\omega/3}(T) \le \underline{R}(T)$ for every $T$.

## Depends on

- [Schönhage's asymptotic sum inequality](asymptotic-sum-inequality.md)

## Sources

- V. Strassen, "Relative bilinear complexity and matrix multiplication", Journal für die reine und angewandte Mathematik 375/376 (1987) 406-443.
- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
- J. Alman, V. Vassilevska Williams, "A refined laser method and faster matrix multiplication", SODA (2021), arXiv:2010.05846.
