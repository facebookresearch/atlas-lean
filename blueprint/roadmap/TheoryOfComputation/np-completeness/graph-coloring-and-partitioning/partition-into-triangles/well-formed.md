# Well-formed simple edge-list instances

An instance consisting of a natural number $n$ and a list $E$ of pairs of natural numbers is well-formed when $E$ has no repeated entries and every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$. This test is shared by PARTITION INTO TRIANGLES, EFFICIENT EDGE DOMINATION and other problems with the same encoding.
