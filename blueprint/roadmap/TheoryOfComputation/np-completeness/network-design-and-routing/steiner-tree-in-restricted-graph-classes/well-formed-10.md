# Well-formed instances of STEINER TREE IN GRAPHS (unit weights) for perfect graphs

An instance $(n, E, R, K)$ of STEINER TREE IN GRAPHS (unit weights) for perfect graphs is well formed when it is a [well-formed STEINER TREE IN GRAPHS instance](../../paths-cycles-and-subgraphs/steiner-tree/well-formed.md), every edge in $E$ has weight $1$, the [graph](../../paths-cycles-and-subgraphs/steiner-tree/graph.md) of all of $E$ on the vertices $0, \dots, n - 1$ is perfect (every induced subgraph has chromatic number equal to its clique number), and $0 < K$.

There is no requirement that $n \ge 1$. With $n = 0$ the well-formed instances are those with $E$ and $R$ empty and $K$ positive; each of them is accepted by the decision problem, because the empty sublist of $E$ has total weight $0$ and joins every pair of terminals vacuously, even though a graph with no vertices has no subtree.
