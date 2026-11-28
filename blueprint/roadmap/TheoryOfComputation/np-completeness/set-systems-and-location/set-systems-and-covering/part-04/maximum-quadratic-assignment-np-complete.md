# MAXIMUM QUADRATIC ASSIGNMENT is NP-complete

The [decision problem](maximum-quadratic-assignment-dec.md) MAXIMUM QUADRATIC ASSIGNMENT belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: with $A$ the adjacency matrix of a clique on $p$ vertices plus $n - p$ isolated vertices and $B$ the adjacency matrix of a graph $G$, the measure is at least $p(p - 1)$ exactly when $G$ has a clique on $p$ vertices (MAX DISPERSION).

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MAXIMUM QUADRATIC ASSIGNMENT.
- E. M. Arkin, R. Hassin and M. Sviridenko, "Approximating the maximum quadratic assignment problem", Information Processing Letters 77 (2001), 13-16, doi:10.1016/S0020-0190(00)00151-4.
