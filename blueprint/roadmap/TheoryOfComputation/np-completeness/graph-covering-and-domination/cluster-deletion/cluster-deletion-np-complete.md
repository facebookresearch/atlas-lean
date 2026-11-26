# CLUSTER DELETION is NP-complete

The following decision problem is NP-complete: it belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it. Given a simple graph $G$ on $\{0, \dots, n - 1\}$, given by a vertex count $n$ and an edge list without repeated edges (in either orientation) or loops, and a natural number $K$, decide whether deleting at most $K$ edges of $G$ makes it a vertex-disjoint union of cliques.

## Sources

- R. Shamir, R. Sharan and D. Tsur, "Cluster graph modification problems", Discrete Applied Mathematics 144(1-2) (2004), 173-182, doi:10.1016/j.dam.2004.01.007 (Theorem 12; NP-completeness first shown by A. Natanzon, *Complexity and approximation of some graph modification problems*, Master's thesis, Tel Aviv University, 1999).
