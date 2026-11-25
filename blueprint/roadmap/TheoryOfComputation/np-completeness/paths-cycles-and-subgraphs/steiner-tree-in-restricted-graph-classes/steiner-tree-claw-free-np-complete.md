# STEINER TREE IN GRAPHS (unit weights) for claw-free graphs is NP-complete

The STEINER TREE IN GRAPHS (unit weights) for claw-free graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a claw-free graph `G = (V, E)` (no induced `K₁,₃`), a set `R ⊆ V` of terminals and a positive integer `K`. Question: is there a subtree of `G` containing every vertex of `R` and having at most `K` edges?

## Sources

- H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van Leeuwen, "Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical Computer Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (arXiv:2004.07492), Lemma 8 ("The unweighted Vertex Steiner Tree problem is NP-complete for line graphs") and the proof of Theorem 2 ("the class of claw-free graphs, which in turn contains the class of line graphs").
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the parent problem).
