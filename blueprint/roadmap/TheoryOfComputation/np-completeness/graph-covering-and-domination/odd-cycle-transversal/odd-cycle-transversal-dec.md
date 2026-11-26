# ODD CYCLE TRANSVERSAL as a decision problem

The decision problem ODD CYCLE TRANSVERSAL
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to an
odd cycle transversal instance $(n, es, K)$ that is well formed and feasible. Well formed means
that $es$ has no repeated entries and every pair $(u, v)$ in $es$ satisfies $u < n$, $v < n$,
$u \ne v$ and $(v, u) \notin es$; feasible means that some set of at most $K$ vertices can be
removed from the graph of the instance so that the remaining induced subgraph is bipartite.
Bitstrings that do not decode to an instance are rejected.
