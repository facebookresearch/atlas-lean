# Well-formed subgraph-isomorphism instances

A subgraph-isomorphism instance
$(n, E_G, m, E_H)$ is well formed when the list $E_G$ has no repeated entries and every
$(u, v) \in E_G$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E_G$, and likewise the
list $E_H$ has no repeated entries and every $(u, v) \in E_H$ satisfies $u < m$, $v < m$,
$u \ne v$ and $(v, u) \notin E_H$.
