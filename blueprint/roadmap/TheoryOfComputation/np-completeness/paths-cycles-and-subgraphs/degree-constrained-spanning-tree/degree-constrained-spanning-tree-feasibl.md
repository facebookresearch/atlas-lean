# Feasibility for DEGREE-CONSTRAINED SPANNING TREE

An instance $(n, E, K)$ of
DEGREE-CONSTRAINED SPANNING TREE is feasible when there is a list $T$ of pairs of natural numbers
such that $T$ is a sublist of $E$ (obtained by deleting entries and keeping the order), $T$ has no
repeated entries, $T$ has exactly $n - 1$ entries, the graph of $T$ on $n$ vertices is connected,
and for every vertex $v < n$ there is no sublist of $T$ with $K + 1$ entries each of which has $v$
as one of its two components.

For a well-formed instance this says that the graph of $E$ on $n$ vertices has a spanning tree in
which every vertex has degree at most $K$.
