# Well-formed pairs of simple edge lists

An instance $(n, E, m, F)$ of two graphs given by vertex counts and edge lists is well-formed when $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$, $v < n$, $u \ne v$ and $(v, u) \notin E$, $F$ has no repeated entries, and every pair $(u, v)$ in $F$ satisfies $u < m$, $v < m$, $u \ne v$ and $(v, u) \notin F$. This test is shared by GRAPH HOMOMORPHISM, GRAPH CONTRACTABILITY and other problems with the same encoding.

The same test is the well-formedness condition of GRAPH MINOR TESTING.
