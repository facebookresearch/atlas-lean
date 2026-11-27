# Feasible MINIMUM FILL-IN instances

An instance $(n, E, K)$ of MINIMUM FILL-IN is
feasible when there are an ordering $\sigma$ of the vertices $0, \dots, n - 1$ (a list that
contains each of them exactly once) and a list $A$ of pairs of natural numbers, with no repeated
entries and at most $K$ entries, such that every pair $(u, v)$ in $A$ satisfies $u < n$, $v < n$
and $u \ne v$, neither $(u, v)$ nor $(v, u)$ belongs to $E$, and $(v, u)$ does not belong to $A$,
and such that, in the graph augmented by $A$, any two distinct vertices $a$ and $b$ that are both
adjacent to a vertex $v$ and both come after $v$ in $\sigma$ are adjacent to each other.

The ordering $\sigma$ is thus a perfect elimination ordering of the augmented graph, so adding
the at most $K$ edges of $A$ to the graph makes it chordal.
