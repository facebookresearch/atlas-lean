# Well-formed simple edge-list instances

An instance consisting of a natural number $n$ and a list $E$ of pairs of natural numbers is well-formed when $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. This test is shared by PARTITION INTO TRIANGLES, EFFICIENT EDGE DOMINATION and other problems with the same encoding.

The same test is the simple edge list of INDUCED SUBGRAPH WITH PROPERTY Π; it imposes no divisibility condition and no bound.
