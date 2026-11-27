# Well-formed weighted independent dominating set instances (chordal)

A weighted independent dominating set instance $(n, E, w, B)$ is well formed when

- the list $E$ has no repeated entries, and every pair $(a, b)$ in $E$ satisfies $a < n$, $b < n$, $a \ne b$, and $(b, a) \notin E$;
- the weight list $w$ has exactly $n$ entries;
- the graph of the instance is chordal: for every $k \ge 4$, the cycle graph $C_k$ is not an induced subgraph of it.
