# STEINER TREE IN GRAPHS with unit weights on chordal graphs is NP-complete

The STEINER TREE IN GRAPHS with unit weights on chordal graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a chordal graph `G = (V, E)` (every cycle of length at least `4` has a chord), a subset `R ⊆ V` of terminals, and a positive integer `K`. Question: is there a subtree of `G` that includes all the vertices of `R` and has at most `K` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
- K. White, M. Farber and W. Pulleyblank, "Steiner trees, connected domination and strongly chordal graphs", Networks 15 (1985), 109-124, doi:10.1002/net.3230150109.
- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1.
- C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the 21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021, Table 1.
