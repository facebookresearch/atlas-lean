# Feasible instances of PARTITION INTO AT MOST K HAMILTONIAN SUBGRAPHS (UNDIRECTED)

An instance $(n, E, K)$ is feasible for PARTITION INTO AT MOST K HAMILTONIAN SUBGRAPHS (UNDIRECTED) when some permutation $\sigma$ of the vertices $0, \dots, n-1$ satisfies: $v$ and $\sigma(v)$ are adjacent in the graph given by $E$ for every $v$ (so $\sigma$ has no fixed point), $\sigma(\sigma(v)) \ne v$ for every $v$, and $\sigma$ has at most $K$ cycles. The cycles of $\sigma$ are then Hamiltonian circuits of the parts of a partition of the vertices into at most $K$ sets of at least three vertices each.
