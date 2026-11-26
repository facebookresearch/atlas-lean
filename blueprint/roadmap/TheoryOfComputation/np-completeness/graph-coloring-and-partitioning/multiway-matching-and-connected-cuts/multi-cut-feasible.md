# Feasible instances of MULTICUT

An instance $(n, E, S, K)$ is feasible for MULTICUT when some sublist $C$ of the weighted edges $E$, of total weight at most $K$, has the property that after deleting the edges of $C$ from the graph on the vertices $0, \dots, n-1$ in which $u$ and $v$ are adjacent when $u \ne v$ and $(u, v, w)$ or $(v, u, w)$ is in $E$ for some $w$, for every pair $(s, t)$ in $S$ the vertex $t$ is not reachable from $s$. A pair with $s = t$ can never be separated, so it makes the instance infeasible.
