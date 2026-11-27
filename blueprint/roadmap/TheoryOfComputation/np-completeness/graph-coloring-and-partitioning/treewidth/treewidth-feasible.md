# Feasible TREEWIDTH instances

An instance $(n, E, K)$ of TREEWIDTH is feasible when the graph $G$ on the vertices $0, \dots, n-1$ in which $u$ and $v$ are adjacent when $u \ne v$ and $(u, v)$ or $(v, u)$ is in $E$ has tree-width at most $K$: for some $N$ there are a tree $T$ on the nodes $0, \dots, N-1$ and finite bags $\beta(x)$ of vertices of $G$, one for each node $x$, such that every vertex lies in some bag, both ends of every edge lie in a common bag, for every vertex $v$ the nodes whose bags contain $v$ induce a connected subgraph of $T$, and every bag has at most $K + 1$ vertices.
