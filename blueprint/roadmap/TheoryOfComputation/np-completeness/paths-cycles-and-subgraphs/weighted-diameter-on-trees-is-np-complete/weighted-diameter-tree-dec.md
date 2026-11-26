# WEIGHTED DIAMETER on trees as a decision problem

The decision problem WEIGHTED DIAMETER on trees accepts a bitstring $x$ exactly when the canonical bitstring decoding of $x$ as a quadruple $(n, E, C, K)$ succeeds and returns an instance that is well formed for the restriction to trees and feasible for WEIGHTED DIAMETER: some rearrangement $\ell$ of $C$, the $k$-th edge of $E$ receiving length $\ell_k$, makes every pair of vertices joined by a path of length at most $K$. Every bitstring that does not decode is rejected.
