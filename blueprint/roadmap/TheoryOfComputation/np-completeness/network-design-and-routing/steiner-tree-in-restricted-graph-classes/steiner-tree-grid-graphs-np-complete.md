# STEINER TREE IN GRAPHS (unit weights) for grid graphs is NP-complete

The STEINER TREE IN GRAPHS (unit weights) for grid graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a grid graph `G = (V, E)`, i.e. a subgraph of the two-dimensional rectilinear grid, a subset `R ⊆ V`, and a positive integer `K`. Question: is there a subtree of `G` that includes all the vertices of `R` and has at most `K` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
- D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Grid", column "StTree" for (unweighted) STEINER TREE IN GRAPHS: "N [35]").
- M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM Journal on Applied Mathematics 32 (1977), 826-834, doi:10.1137/0132071.
