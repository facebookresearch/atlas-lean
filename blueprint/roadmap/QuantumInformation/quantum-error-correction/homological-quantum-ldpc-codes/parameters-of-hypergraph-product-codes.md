# Parameters of hypergraph product codes

Let $C_i = \ker H_i$ and $C_i^{T} = \ker H_i^{T}$ have dimensions $k_i, k_i^{T}$ and minimum distances $d_i, d_i^{T}$ (with the convention $d = \infty$ for the zero code). Then the hypergraph product satisfies $H_X H_Z^{T} = 0$, has dimension $k = k_1 k_2 + k_1^{T} k_2^{T}$, and minimum distance $d = \min(d_1, d_2, d_1^{T}, d_2^{T})$. If $H_1 = H_2$ is the check matrix of a $(\Delta_V, \Delta_C)$-regular classical LDPC code of rate $R > 0$ and relative distance $\delta > 0$, the hypergraph product is a quantum LDPC family with $k = \Theta(n)$ and $d = \Theta(\sqrt n)$.

## Proof sketch

$H_X H_Z^{T} = H_1 \otimes H_2^{T} + H_1 \otimes H_2^{T} = 0$ over $\mathbb{F}_2$. The Künneth formula gives the homology of a tensor product of complexes, hence the dimension. For the distance, a nontrivial $Z$-logical restricted to a row or column of the $n_1 \times n_2$ block projects to a nonzero codeword of $C_1$ or $C_2$ (or of the transposes on the second block), so has weight at least the corresponding classical distance; matching upper bounds come from logical operators supported on single rows or columns.

## Depends on

- [Hypergraph product of two classical codes (Tillich-Zemor)](hypergraph-product-of-classical-codes.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Proof depends on

- [Hypergraph product of two classical codes (Tillich-Zemor)](hypergraph-product-of-classical-codes.md)
- [Quantum LDPC code families and asymptotically good quantum codes](quantum-ldpc-code-families-and-good-codes.md)

## Sources

- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566.
