# Parameters of hypergraph product codes

Let $C_i = \ker H_i$ and $C_i^{T} = \ker H_i^{T}$ have dimensions $k_i, k_i^{T}$ and minimum distances $d_i, d_i^{T}$ (with the convention $d = \infty$ for the zero code). Then the hypergraph product satisfies $H_X H_Z^{T} = 0$, has dimension $k = k_1 k_2 + k_1^{T} k_2^{T}$, and minimum distance

$$
d \ge \min(d_1, d_2, d_1^{T}, d_2^{T}) .
$$

Equality holds when the minimum is attained by some $d_i$ whose partner code $C_{3-i}$ is nonzero ($d_{3-i} \ne \infty$), or by some $d_i^{T}$ whose partner code $C_{3-i}^{T}$ is nonzero ($d_{3-i}^{T} \ne \infty$); in general $d \le d_i$ whenever $C_{3-i} \ne 0$ and $d \le d_i^{T}$ whenever $C_{3-i}^{T} \ne 0$. Without these hypotheses the minimum is only a lower bound: for $H_1 = \begin{pmatrix} 1 & 1 \\ 0 & 0 \end{pmatrix}$ and $H_2 = (1\ 1)$ the four classical distances are $d_1 = 2$, $d_1^{T} = 1$, $d_2 = 2$, $d_2^{T} = \infty$, but both quantum distances are $2$. If $H_1 = H_2$ is a full-row-rank check matrix (so that $\ker H_1^{T} = 0$) of a $(\Delta_V, \Delta_C)$-regular classical LDPC code of rate $R > 0$ and relative distance $\delta > 0$, the hypergraph product is a quantum LDPC family with $k = \Theta(n)$ and $d = \Theta(\sqrt n)$.

## Proof sketch

$H_X H_Z^{T} = H_1 \otimes H_2^{T} + H_1 \otimes H_2^{T} = 0$ over $\mathbb{F}_2$. The Künneth formula gives the homology of a tensor product of complexes, hence the dimension. For the lower bound on the distance, a codeword of $C_X$ of weight below the minimum is shown, block by block, to be a sum of rows of $H_Z$, using that its restrictions to rows or columns of the two blocks lie in the classical codes. For the upper bound $d \le d_1$ when $C_2 \ne 0$: take $x_1 \in C_1$ of weight $d_1$ and a position $y$ with the unit vector $e_y \notin C_2^{\perp}$, which exists because $C_2 \ne 0$; then $x_1 \otimes e_y$ lies in $C_X$ but not in $C_Z^{\perp}$. The other three upper bounds are analogous. With $H_1 = H_2$ of full row rank, $C_1 = C_2 \ne 0$, so equality holds.

## Depends on

- [Hypergraph product of two classical codes (Tillich-Zemor)](hypergraph-product-of-classical-codes.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Sources

- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566, Theorem 15, Lemmas 16 and 17.
