# Well-formed weighted radius instances on trees

A WEIGHTED RADIUS instance $(n, E, C, K)$ (vertex count $n$, edge list $E$, list $C$ of edge lengths, bound $K$) is well formed for trees when

- the list $E$ has no repeated entries, and every pair $(a, b)$ in $E$ satisfies $a < n$, $b < n$, $a \ne b$, and $(b, a) \notin E$;
- $C$ has as many entries as $E$;
- $K > 0$;
- the graph on $\{0, \dots, n-1\}$ in which distinct $u, v$ are adjacent when $(u, v) \in E$ or $(v, u) \in E$ is a tree.
