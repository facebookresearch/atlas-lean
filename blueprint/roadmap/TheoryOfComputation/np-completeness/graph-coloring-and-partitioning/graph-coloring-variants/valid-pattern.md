# Valid H-COLORING patterns

A pattern $(m, F)$, with $m$ a natural number and $F$ a list of pairs of natural numbers, is valid for H-COLORING when $F$ has no repeated entries, every pair $(u, v)$ in $F$ satisfies $u < m$, $v < m$, $u \ne v$ and $(v, u) \notin F$, and the graph $H$ on $\{0, \dots, m-1\}$ with edge list $F$ is not bipartite.
