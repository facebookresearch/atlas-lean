# Broadcast steps

For an instance with graph $G$, sets $V'$ and $V''$ of vertices and a set $F$ of edges, $(V', F, V'')$ is a broadcast step when $F \subseteq E(G)$, each edge of $F$ has exactly one endpoint in $V'$, no two edges of $F$ share an endpoint, and $V'' = V' \cup \{v : \{u, v\} \in F\}$.
