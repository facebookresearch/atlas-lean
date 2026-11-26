# Feasible MINIMUM CUT LINEAR ARRANGEMENT instances

A one-to-one numbering of the vertices, given by the positions in a permutation `perm` of $0, \dots, n - 1$, such that for every cut position $j$ with $j + 1 < n$ at most $K$ entries $(u, v)$ of the edge list have one endpoint at a position $\le j$ and the other at a position $> j$ (a vertex not in `perm` has position $n$). Entries are counted, so $(0, 1)$ and $(1, 0)$ count twice; for a simple edge list, which well-formedness checks, this counts the edges across the cut.
