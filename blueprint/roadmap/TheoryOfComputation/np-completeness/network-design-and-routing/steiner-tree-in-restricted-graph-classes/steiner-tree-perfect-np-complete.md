# STEINER TREE IN GRAPHS (unit weights) for perfect graphs is NP-complete

The [STEINER TREE IN GRAPHS (unit weights) for perfect graphs decision problem](steiner-tree-perfect-dec.md) lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a [well-formed instance](well-formed-10.md) $(n, E, R, K)$: a vertex count $n$ (possibly $0$), a list $E$ of weighted edges $(u, v, 1)$ forming a perfect simple graph $G$ on the vertices $0, \dots, n - 1$, a list $R$ of distinct terminals of $G$ and a positive integer $K$. Question: is there a sublist $T$ of $E$ whose weights sum to at most $K$ (with unit weights, $T$ has at most $K$ entries) such that any two terminals in $R$ are joined by a path in the graph of $T$? This is the [STEINER TREE IN GRAPHS feasibility condition](../../paths-cycles-and-subgraphs/steiner-tree/steiner-tree-feasible.md). When $n \ge 1$ it is equivalent to asking for a subtree of $G$ with at most $K$ edges that contains every vertex of $R$. When $n = 0$ there is no subtree, but $E$ and $R$ are empty and the empty sublist joins every pair of terminals vacuously, so every well-formed instance with no vertices is a yes-instance.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS.
- H. Müller and A. Brandstädt, "The NP-completeness of Steiner tree and dominating set for chordal bipartite graphs", Theoretical Computer Science 53 (1987), 257-265, doi:10.1016/0304-3975(87)90067-3.
- D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1.
- C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the 21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021, Table 1.
