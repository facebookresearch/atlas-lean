# DOMINATING SET as a decision problem

The decision problem DOMINATING SET accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a triple
$(n, E, K)$ of a natural number $n$, a list $E$ of pairs of natural numbers and a natural number
$K$ such that $E$ has no repeated entries, every pair $(u, v) \in E$ satisfies $u < n$, $v < n$,
$u \ne v$ and $(v, u) \notin E$, and there is a set $S$ of at most $K$ vertices with every vertex
in $S$ or adjacent to a vertex of $S$, in the graph on $\{0, \dots, n - 1\}$ where distinct $i$
and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $E$. Bitstrings that do not decode are
rejected.
