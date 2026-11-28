# Directed path graphs

A graph $G$ on vertices $0, \dots, n-1$ is a directed path graph when there are a tree $T$ on
$\{0, \dots, m-1\}$, an orientation $D$ of the edges of $T$, and for each vertex $v$ of $G$ a
set $P_v$ of vertices of $T$ that is the vertex set of a path of $T$ all of whose edges follow
$D$, such that distinct vertices $u$ and $v$ are adjacent in $G$ exactly when $P_u$ and $P_v$
share a vertex.
