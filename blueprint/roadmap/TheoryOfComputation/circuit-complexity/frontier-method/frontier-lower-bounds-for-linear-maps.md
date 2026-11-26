# Frontier lower bounds for linear maps with totally regular matrices

A matrix is *totally regular* if all of its square submatrices are nonsingular (for example the Cauchy matrix $\bigl(1/(i-(N+j))\bigr)_{i,j}$ over a field of characteristic zero or a large prime field). For every fan-in $r\ge2$, every $\varepsilon>0$ and all large $N$, every circuit of fan-in at most $r$ computing a totally regular linear map $F^N\to F^N$ has $s$ inner gates with $(r-1)s>(2-\varepsilon)N$, over finite fields with any basis and over infinite fields with polynomial operations. In particular every arithmetic circuit of additions, multiplications and constants computing $x\mapsto\bigl(\sum_j x_j/(i-N-j)\bigr)_i$ uses more than $(2-\varepsilon)N$ additions and multiplications.

## Proof sketch

For a linear map the demand at a cut comes from the rank of the submatrix between revealed inputs and outputs: total regularity makes every such submatrix of full rank, so a layout must cut nearly $\min$ of the two sides many edges at some step, which with spanning-tree layouts gives the coefficient $2$.

## Depends on

- [Arithmetic circuit](../../algebraic-complexity/arithmetic-circuits/arithmetic-circuit.md)
- [Layouts of multigraphs, cycle rank and the layout hypothesis](layouts-and-the-layout-hypothesis.md)

## Proof depends on

- [Spanning-tree layouts give the layout hypothesis with A = 1](spanning-tree-layouts.md)
- [From small circuits to wide constraint networks](from-circuits-to-constraint-networks.md)

## Sources

- Serge Gaspers, "Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms", 2026.
- Leslie G. Valiant, "Graph-Theoretic Arguments in Low-Level Complexity", Mathematical Foundations of Computer Science 1977, 1977.
- Peter Bürgisser, Michael Clausen, M. Amin Shokrollahi, "Algebraic Complexity Theory", Springer, 1997.
