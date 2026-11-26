# STEINER TREE IN GRAPHS with unit weights is NP-complete

For every natural number `k` with `4 ≤ k`, the STEINER TREE IN GRAPHS with unit weights decision problem with parameter `k` lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` in which no vertex has degree exceeding `k`, a subset `R ⊆ V`, and a positive integer bound `B`. Question: is there a subtree of `G` that includes all the vertices of `R` and has at most `B` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, pp. 208-209 (the problem; NP-complete with equal edge weights, even for planar graphs).
- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (unweighted STEINER TREE IN GRAPHS is NP-complete for degree-`k` graphs, `k` fixed, and for grid graphs, the latter citing Garey and Johnson 1977).
- M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM J. Appl. Math. 32 (1977), 826-834, doi:10.1137/0132071.
