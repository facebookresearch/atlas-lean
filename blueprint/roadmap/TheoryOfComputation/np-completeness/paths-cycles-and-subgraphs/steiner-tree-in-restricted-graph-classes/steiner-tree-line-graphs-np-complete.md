# STEINER TREE IN GRAPHS (unit weights) for line graphs is NP-complete

The STEINER TREE IN GRAPHS (unit weights) for line graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a graph `G = (V, E)` that is an edge (line) graph, a subset `R ⊆ V`, and a positive integer `K`. Question: is there a subtree of `G` that includes all the vertices of `R` and has at most `K` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
- D. S. Johnson, "The NP-completeness column: an ongoing guide" (sixteenth edition), Journal of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "Edge (or Line)", column "StTree" for (unweighted) STEINER TREE IN GRAPHS: "N [70]", reference [70] being a private communication of A. Schaffer).
- H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van Leeuwen, "Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical Computer Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (Lemma 8 and Observation 1).
