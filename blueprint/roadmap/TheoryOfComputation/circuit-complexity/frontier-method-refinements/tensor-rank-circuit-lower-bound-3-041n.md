# Fan-in-two circuit lower bounds of 3.041n from 3-tensor rank

Partition the coordinates of $S\subseteq U^n$ into three parts by $p:\{1,\dots,n\}\to\{0,1,2\}$ and let $\mathcal{T}_p(S)$ be the $3$-tensor whose $(a,b,c)$ entry is $1$ iff the input with parts $a,b,c$ lies in $S$. If a fan-in-two circuit decides $S$, a balanced planar Gaussian $3$-way cut of its (subcubic) constraint network shows that $\mathcal{T}_p(S)$ is a restriction of the matrix multiplication tensor $\langle D,D,D\rangle$ with $D=|U|^{\max(|E_{01}|,|E_{12}|,|E_{20}|)}$ for suitable $p$, so its tensor rank is at most the rank of $\langle D,D,D\rangle$, which is at most $D^{3}$ and at most $D^{\omega+o(1)}$. Consequently functions whose three-part tensors have nearly full rank under every balanced tripartition require fan-in-two circuits with more than $(3.041-o(1))n$ multiary gates; such functions exist by counting.

## Proof sketch

A $\mathbb{Z}_3$-symmetric planar Gaussian embedding of a subcubic multigraph yields a balanced $3$-way vertex cut whose three pairwise cuts each contain few edges in expectation (an explicit rational mismatch coefficient); splicing the network along the three cuts writes the indicator tensor as a restriction of a square matrix multiplication tensor, and counting shows most functions have high-rank tensors.

## Depends on

- [Rectangle-free sets and rectangle bias](../frontier-method/rectangle-free-sets-and-rectangle-bias.md)
- [Tensor rank](../../algebraic-complexity/matrix-multiplication-exponent/tensor-rank.md)
- [Matrix multiplication tensor](../../algebraic-complexity/matrix-multiplication-exponent/matrix-multiplication-tensor.md)

## Proof depends on

- [From small circuits to wide constraint networks](../frontier-method/from-circuits-to-constraint-networks.md)
- [Unconditional frontier lower bounds of (2 - ε)n](../frontier-method/unconditional-frontier-lower-bounds.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
