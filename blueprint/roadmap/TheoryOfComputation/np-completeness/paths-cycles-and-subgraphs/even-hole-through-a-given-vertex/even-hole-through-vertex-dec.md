# EVEN HOLE THROUGH A GIVEN VERTEX as a decision problem

The decision problem EVEN HOLE THROUGH A GIVEN VERTEX accepts a bitstring $x$ exactly when $x$
decodes, under the canonical bitstring encoding of its instances, to an instance $(n, E, v)$
whose edge list describes a simple graph on $\{0, \dots, n-1\}$ (no duplicate edges in either
orientation, no loops, endpoints less than $n$) with $v < n$, and that is
[feasible](even-hole-through-vertex-feasible.md). It rejects every bitstring that does not
decode to an instance.
