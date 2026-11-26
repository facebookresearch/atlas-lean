# STEINER TREE IN GRAPHS (unit weights) for claw-free graphs is NP-complete

The [STEINER TREE IN GRAPHS (unit weights) for claw-free graphs decision problem](steiner-tree-claw-free-dec.md) lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a [well-formed instance](well-formed-5.md) $(n, E, R, K)$: a vertex count $n$ (possibly $0$), a list $E$ of weighted edges $(u, v, 1)$ forming a claw-free simple graph $G$ on the vertices $0, \dots, n - 1$ (no induced $K_{1,3}$), a list $R$ of distinct terminals of $G$ and a positive integer $K$. Question: is there a sublist $T$ of $E$ whose weights sum to at most $K$ (with unit weights, $T$ has at most $K$ entries) such that any two terminals in $R$ are joined by a path in the graph of $T$? This is the [STEINER TREE IN GRAPHS feasibility condition](../../paths-cycles-and-subgraphs/steiner-tree/steiner-tree-feasible.md). When $n \ge 1$ it is equivalent to asking for a subtree of $G$ with at most $K$ edges that contains every vertex of $R$. When $n = 0$ there is no subtree, but $E$ and $R$ are empty and the empty sublist joins every pair of terminals vacuously, so every well-formed instance with no vertices is a yes-instance.

## Sources

- H. L. Bodlaender, N. Brettell, M. Johnson, G. Paesani, D. Paulusma and E. J. van Leeuwen, "Steiner trees for hereditary graph classes: a treewidth perspective", Theoretical Computer Science 867 (2021), 30-39, doi:10.1016/j.tcs.2021.03.012 (arXiv:2004.07492), Lemma 8 ("The unweighted Vertex Steiner Tree problem is NP-complete for line graphs") and the proof of Theorem 2 ("the class of claw-free graphs, which in turn contains the class of line graphs").
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS (the parent problem).
