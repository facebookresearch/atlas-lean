# Nisan's characterization of non-commutative ABP size

For a nonzero homogeneous non-commutative polynomial $f$ of degree $d\ge1$ and $0\le k\le d$, let $M_k(f)$ be the matrix with rows indexed by words $u$ of length $k$, columns by words $v$ of length $d-k$, and entries the coefficients of $uv$ in $f$. Then the minimum size of a homogeneous layered non-commutative ABP computing $f$ equals $\sum_{k=0}^{d}\operatorname{rank}M_k(f)$ (the terms $k=0$ and $k=d$ equal $1$, for the source and the sink).

## Proof sketch

Lower bound: the number of vertices in layer $k$ is at least $\operatorname{rank}M_k(f)$, since $M_k$ factors through the vector of partial path sums into layer $k$. Upper bound: take as layer-$k$ vertices a basis of the row space of $M_k(f)$ (the span of the 'rows' $v\mapsto\mathrm{coeff}(uv,f)$), with transitions given by left multiplication by a variable.

## Depends on

- [Non-commutative arithmetic circuits and algebraic branching programs](non-commutative-circuits-and-abps.md)

## Sources

- Noam Nisan, "Lower Bounds for Non-Commutative Computation", Proceedings of the 23rd Annual ACM Symposium on Theory of Computing, 1991.
- Ramprasad Saptharishi, "A survey of lower bounds in arithmetic circuit complexity", version 9.0.3, 2021, Chapter 11.
