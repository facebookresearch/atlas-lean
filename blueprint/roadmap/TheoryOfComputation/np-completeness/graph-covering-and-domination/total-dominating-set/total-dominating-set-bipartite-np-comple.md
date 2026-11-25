# TOTAL DOMINATING SET on bipartite graphs is NP-complete

The TOTAL DOMINATING SET on bipartite graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a bipartite graph `G = (V, E)` with no isolated vertices, and a positive integer `K ≤ |V|`. Question: does `G` have a total dominating set of size at most `K`, i.e. a set `D ⊆ V` with `|D| ≤ K` such that every vertex of `V` (including those in `D`) is adjacent to a vertex of `D`?

## Sources

- J. Pfaff, R. C. Laskar and S. T. Hedetniemi, "NP-completeness of total and connected domination and irredundance for bipartite graphs", Technical Report 428, Department of Mathematical Sciences, Clemson University (1983).
- M. A. Shalu and V. K. Kirubakaran, "Total domination and open packing in some subclasses of bipartite graphs", Journal of Combinatorial Optimization 50(5) (2025), article 44, doi:10.1007/s10878-025-01360-w (NP-completeness on a subclass of bipartite graphs; cites the technical report).
