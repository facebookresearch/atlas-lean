# STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most k (fixed k ≥ 1) is NP-complete

For every natural number `k` with `1 ≤ k`, the STEINER TREE IN GRAPHS (unit weights) on graphs of thickness at most k (fixed k ≥ 1) decision problem with parameter `k` lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` of thickness at most `k` with weight `w(e) = 1` for each `e ∈ E`, a subset `R ⊆ V`, and a positive integer bound `B`. Question: is there a subtree of `G` that includes all the vertices of `R` and such that the sum of the weights of the edges in the subtree (its number of edges) is no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment ("Remains NP-complete if all edge weights are equal, even if [...] G is planar [Garey and Johnson, 1977a]").
- M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM Journal on Applied Mathematics 32(4) (1977), 826-834, doi:10.1137/0132071.
- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3) (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Section 3 (thickness-k graphs) and Table 1 (thickness-k graphs, unweighted STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson).
