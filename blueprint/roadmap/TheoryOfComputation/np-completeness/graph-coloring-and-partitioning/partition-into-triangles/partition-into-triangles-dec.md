# PARTITION INTO TRIANGLES as a decision problem

The decision problem PARTITION INTO
TRIANGLES accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
encoding, to an instance consisting of a natural number $n$ and a list $E$ of pairs of natural
numbers such that $E$ has no repeated entries, every pair $(u, v)$ in $E$ satisfies $u < n$,
$v < n$, $u \ne v$ and $(v, u) \notin E$, and the vertex set $\{0, \dots, n - 1\}$ can be
partitioned into sets of three vertices, any two of which are adjacent in the graph of $E$ on $n$
vertices. Bitstrings that do not decode to an instance are rejected.
