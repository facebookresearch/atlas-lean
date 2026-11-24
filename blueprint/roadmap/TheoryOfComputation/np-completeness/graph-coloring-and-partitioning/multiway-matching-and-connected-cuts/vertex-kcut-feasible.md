# Feasible instances of VERTEX K-CUT

An instance $(n, E, P, w, K)$ is feasible for VERTEX K-CUT when some set $C$ of vertices, containing no vertex of any listed pair and of total weight at most $K$ (the sum of the listed weights $w_v$ over $v \in C$), disconnects every pair: in the subgraph of the graph on the vertices $0, \dots, n-1$ in which $u$ and $v$ are adjacent when $u \ne v$ and $(u, v)$ or $(v, u)$ is in $E$ induced on the vertices outside $C$, $t_i$ is not reachable from $s_i$ for every pair $(s_i, t_i)$ in $P$. A pair with $s_i = t_i$ can never be separated.
