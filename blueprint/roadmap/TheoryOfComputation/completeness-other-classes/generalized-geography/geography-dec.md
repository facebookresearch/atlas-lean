# Geography as a decision problem

The Geography decision problem accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, s)$ of a
natural number, a list of pairs of natural numbers and a natural number, to a triple with
$s < n$, with both entries of every pair in $E$ less than $n$, and with
$\mathrm{GeoWins}(n + 1, E, s, [s])$, where $[s]$ is the list whose only entry is $s$.
Bitstrings that do not decode are rejected.

A play never revisits one of the $n$ vertices, so the fuel $n + 1$ never runs out: the condition
says that the player who moves first wins Geography on the directed graph with vertices
$0, \ldots, n - 1$ and edge list $E$, with the token starting on $s$ and $s$ marked visited.
