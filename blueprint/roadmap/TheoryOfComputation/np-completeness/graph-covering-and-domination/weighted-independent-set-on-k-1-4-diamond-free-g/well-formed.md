# Well-formed weighted independent set instances ($K_{1,4}$, diamond)

A weighted independent set instance $(n, E, w, k)$ is well formed when

- the list $E$ has no repeated entries, and every pair $(a, b)$ in $E$ satisfies $a < n$, $b < n$, $a \ne b$, and $(b, a) \notin E$;
- the weight list $w$ has exactly $n$ entries;
- the graph of the instance has no induced subgraph isomorphic to the star $K_{1,4}$;
- the graph of the instance has no induced subgraph isomorphic to the diamond, the complete graph $K_4$ on $\{0,1,2,3\}$ with the edge $\{0,1\}$ removed.
