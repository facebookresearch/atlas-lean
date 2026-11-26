# Well-formed edge-list instances with a positive bound

An instance $(n, E, K)$ is well-formed when the list $E$ is a simple edge list, as for a well-formed GRAPH COLORING instance (no repeated entries, and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$), and $K > 0$. This test is shared by ACYCLIC COLORING, CHROMATIC SUM, GRUNDY NUMBER, EDGE RANKING, GRAPH THICKNESS, H-MATCHING and other problems with the same encoding. Listing the reversed copy of an edge makes an instance malformed although it does not change the graph.
