# Well-formed instances of STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree at most k

For a natural number $k$, an instance $(n, E, R, B)$ of STEINER TREE IN GRAPHS with unit weights on graphs of maximum degree at most $k$ is well formed when it is a [well-formed STEINER TREE IN GRAPHS instance](../../paths-cycles-and-subgraphs/steiner-tree/well-formed.md), every edge in $E$ has weight $1$, every vertex of the [graph](../../paths-cycles-and-subgraphs/steiner-tree/graph.md) of all of $E$ on the vertices $0, \dots, n - 1$ has degree at most $k$, and $0 < B$.

There is no requirement that $n \ge 1$. With $n = 0$ the well-formed instances are those with $E$ and $R$ empty and $B$ positive, for every $k$; each of them is accepted by the decision problem, because the empty sublist of $E$ has total weight $0$ and joins every pair of terminals vacuously, even though a graph with no vertices has no subtree.
