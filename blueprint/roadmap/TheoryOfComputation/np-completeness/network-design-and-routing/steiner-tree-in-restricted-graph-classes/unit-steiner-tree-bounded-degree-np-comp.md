# STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree at most k is NP-complete for every fixed k ≥ 4

For every natural number $k$ with $4 \le k$, the [STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree at most k decision problem](unit-steiner-tree-bounded-degree-dec.md) with parameter $k$ lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a [well-formed instance](well-formed-14.md) $(n, E, R, B)$: a vertex count $n$ (possibly $0$), a list $E$ of weighted edges $(u, v, 1)$ forming a simple graph $G$ on the vertices $0, \dots, n - 1$ in which no vertex has degree exceeding $k$, a list $R$ of distinct terminals of $G$ and a positive integer bound $B$. Question: is there a sublist $T$ of $E$ whose weights sum to at most $B$ (with unit weights, $T$ has at most $B$ entries) such that any two terminals in $R$ are joined by a path in the graph of $T$? This is the [STEINER TREE IN GRAPHS feasibility condition](../../paths-cycles-and-subgraphs/steiner-tree/steiner-tree-feasible.md). When $n \ge 1$ it is equivalent to asking for a subtree of $G$ with at most $B$ edges that contains every vertex of $R$. When $n = 0$ there is no subtree, but $E$ and $R$ are empty and the empty sublist joins every pair of terminals vacuously, so every well-formed instance with no vertices is a yes-instance.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND12] STEINER TREE IN GRAPHS, pp. 208-209 (the problem; NP-complete with equal edge weights, even for planar graphs).
- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 6 (1985), 434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (unweighted STEINER TREE IN GRAPHS is NP-complete for degree-$k$ graphs, $k$ fixed, and for grid graphs, the latter citing Garey and Johnson 1977).
- M. R. Garey and D. S. Johnson, "The rectilinear Steiner tree problem is NP-complete", SIAM J. Appl. Math. 32 (1977), 826-834, doi:10.1137/0132071.
