# STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph is NP-complete

The STEINER TREE IN GRAPHS with unit weights, terminals forming one side of a bipartite graph decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a bipartite graph `G = (V, E)` with all edge weights equal to 1 and no edge joining two vertices in `R` or two vertices in `V − R`, a subset `R ⊆ V`, and a positive integer `B`. Question: is there a subtree of `G` that includes all the vertices of `R` and has at most `B` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, p. 209 (comment: "Remains NP-complete if all edge weights are equal, even if G is a bipartite graph having no edges joining two vertices in R or two vertices in V−R [Berlekamp, 1976]").
