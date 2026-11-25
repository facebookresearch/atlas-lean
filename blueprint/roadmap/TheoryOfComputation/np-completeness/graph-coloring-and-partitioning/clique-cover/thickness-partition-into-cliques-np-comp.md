# PARTITION INTO CLIQUES for graphs of thickness at most k is NP-complete

For every natural number `k` with `1 ≤ k`, the PARTITION INTO CLIQUES for graphs of thickness at most k decision problem with parameter `k` lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` of thickness at most `k` and a positive integer `K ≤ |V|`. Question: can `V` be partitioned into at most `K` disjoint sets each of which induces a clique?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT15] PARTITION INTO CLIQUES.
- M. R. Cerioli, L. Faria, T. O. Ferreira, C. A. J. Martinhon, F. Protti and B. Reed, "Partition into cliques for cubic graphs: Planar case, complexity and approximation", Discrete Applied Mathematics 156(12) (2008), 2270-2278, doi:10.1016/j.dam.2007.10.015 (NP-complete for planar cubic graphs).
- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (PARTITION INTO CLIQUES on planar and on thickness-`k` graphs: NP-complete, citing F. Berman, D. S. Johnson, F. T. Leighton, P. W. Shor and L. Snyder, "Generalized planar matching", manuscript, 1985).
