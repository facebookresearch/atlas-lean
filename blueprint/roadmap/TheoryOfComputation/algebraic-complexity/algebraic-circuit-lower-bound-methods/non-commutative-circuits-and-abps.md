# Non-commutative arithmetic circuits and algebraic branching programs

A *non-commutative polynomial* over $K$ in variables $X=\{x_1,\dots,x_n\}$ is an element of the free algebra $K\langle X\rangle$ (a linear combination of words). An arithmetic circuit computes a non-commutative polynomial when evaluated in $K\langle X\rangle$ with ordered multiplication. A *homogeneous layered non-commutative algebraic branching program* (ABP) of degree $d$ has vertex layers $0,\dots,d$, a source in layer $0$, a sink in layer $d$, and edges from layer $i$ to $i+1$ labelled by homogeneous linear forms $\sum_jc_jx_j$ in $X$; it computes the sum over source–sink paths of the ordered products of edge labels. Its size is its number of vertices.

## Depends on

- [Arithmetic circuit](../arithmetic-circuits/arithmetic-circuit.md)

## Sources

- Noam Nisan, "Lower Bounds for Non-Commutative Computation", Proceedings of the 23rd Annual ACM Symposium on Theory of Computing, 1991.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Chapter 11.
