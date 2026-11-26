# STEINER TREE IN GRAPHS (unit weights) on comparability graphs is NP-complete

The STEINER TREE IN GRAPHS (unit weights) on comparability graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a comparability graph `G = (V, E)` with weight `w(e) = 1` for each `e ∈ E`, a subset `R ⊆ V`, and a positive integer bound `B`. Question: is there a subtree of `G` that includes all the vertices of `R` and such that the sum of the weights of the edges in the subtree (its number of edges) is no more than `B`?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, comment ("Remains NP-complete if all edge weights are equal, even if G is a bipartite graph having no edges joining two vertices in R or two vertices in V-R [Berlekamp, 1976]").
- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3) (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (comparability graphs, unweighted STEINER TREE IN GRAPHS: NP-complete, citing Garey and Johnson).
- H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal bipartite graphs", Theoretical Computer Science 53(2-3) (1987), 257-265, doi:10.1016/0304-3975(87)90067-3.
