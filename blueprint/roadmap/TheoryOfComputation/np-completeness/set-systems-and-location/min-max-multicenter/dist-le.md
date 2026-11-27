# Dist LE

For a vertex $v$, a triple $p = (a, b, t)$ and a real number $r$: some walk from $v$ reaches $a$ with total length plus $t$ at most $r$, or some walk from $v$ reaches $b$ with total length plus $\ell(\{a, b\}) - t$ at most $r$. The triple need not be a point on the graph; for example, on the one-vertex graph, $v = a = b$ and $t = 1$ satisfy the second inequality with $r = -1$. When $p$ is a [point on the graph](on-graph.md), as feasibility checks separately, the condition says that the shortest-path distance from $v$ to $p$ is at most $r$.
