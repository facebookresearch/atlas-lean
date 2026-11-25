# FIXED-POINT-FREE AUTOMORPHISM is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, decide whether $G$ has an automorphism that fixes no vertex, that is, a bijection $f$ of the vertices preserving adjacency and non-adjacency with $f(v) \ne v$ for every vertex $v$ (the graph with no vertices is a yes-instance).

## Sources

- A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing 10 (1981), 11-21, doi:10.1137/0210002.
- A. Abiad, G. Coutinho, E. Juliano, V. F. dos Santos and S. Zeijlemaker, "Computing fixed point free automorphisms of graphs", arXiv:2603.26006 (2026), Section 1.
