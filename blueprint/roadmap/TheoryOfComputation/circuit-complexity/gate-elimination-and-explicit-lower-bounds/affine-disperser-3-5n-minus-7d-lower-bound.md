# A 3.5n - 7d lower bound for affine dispersers

Every circuit over the full binary basis $B_2$ computing an affine disperser for dimension $d$ on $n$ bits contains at least $3.5n-7d$ genuinely binary gates; in particular its size is at least $3.5n-7d$. With known explicit affine dispersers for dimension $d=o(n)$ this gives explicit functions in $\mathsf{P}$ requiring $B_2$-circuits of size $3.5n-o(n)$, improving the earlier bounds $(3+\tfrac1{86})n-o(n)$ and $3.1n-o(n)$.

## Proof sketch

Gate elimination on fair semi-circuits with a potential function combining gates, parameters and affine constraints. Each step restricts the input by one affine equation (keeping the disperser nonconstant while the dimension exceeds $d$) and removes on average at least $3.5$ gates per eliminated degree of freedom, using deletions of degenerate gates and a careful case analysis around a minimal AND-type gate.

## Depends on

- [Affine dispersers](affine-dispersers.md)
- [The full binary basis B2 and the basis U2](../circuit-models-and-complexity-measures/full-binary-basis-b2-and-u2.md)

## Proof depends on

- [Fair semi-circuits over the full binary basis](fair-semi-circuits.md)

## Sources

- Om Swostik Mishra, Rahul Santhanam, "An Explicit 3.5n - o(n) Size Lower Bound against General Boolean Circuits", Electronic Colloquium on Computational Complexity, 2026.
- Magnus Gausdal Find, Alexander Golovnev, Edward A. Hirsch, Alexander S. Kulikov, "A Better-than-3n Lower Bound for the Circuit Complexity of an Explicit Function", IEEE 57th Annual Symposium on Foundations of Computer Science, 2016.
- Jiatu Li, Tianqi Yang, "3.1n - o(n) Circuit Lower Bounds for Explicit Functions", Proceedings of the 54th Annual ACM Symposium on Theory of Computing, 2022.
