# Binary chain complexes of length two and their homology

A *binary chain complex of length two* is a sequence of finite-dimensional $\mathbb{F}_2$-vector spaces with fixed bases and linear maps

$$
C_2 \xrightarrow{\ \partial_2\ } C_1 \xrightarrow{\ \partial_1\ } C_0, \qquad \partial_1 \partial_2 = 0 .
$$

Its homology is $H_1 = \ker \partial_1 / \mathrm{im}\, \partial_2$ and its cohomology is $H^1 = \ker \partial_2^{T} / \mathrm{im}\, \partial_1^{T}$, where transposes are taken with respect to the fixed bases; $\dim H_1 = \dim H^1$. The Hamming weight $|c|$ of $c \in C_i$ is its number of nonzero coordinates.

## Sources

- Jean-Pierre Tillich, Gilles Zemor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60(2) (2014); arXiv:0903.0566.
- Nikolas P. Breuckmann, Jens N. Eberhardt, "Balanced product quantum codes", IEEE Transactions on Information Theory 67(10) (2021); arXiv:2012.09271.
