# STEINER TREE IN GRAPHS (unit weights) for undirected path graphs is NP-complete

The STEINER TREE IN GRAPHS (unit weights) for undirected path graphs decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: an undirected path graph `G = (V, E)`, that is, the vertex intersection graph of a family of paths in an undirected tree, a set `R ⊆ V` of terminals and a positive integer `K`. Question: is there a subtree of `G` containing every vertex of `R` and having at most `K` edges?

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the parent problem).
- C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the 21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021 (arXiv:2104.14395), Section 4, Corollary 5 ("STEINER TREE is NP-complete when restricted to undirected path graphs of diameter at most 3"), and Table 1 (STEINER TREE on UNDIRECTED PATH graphs: N Thm. 4).
