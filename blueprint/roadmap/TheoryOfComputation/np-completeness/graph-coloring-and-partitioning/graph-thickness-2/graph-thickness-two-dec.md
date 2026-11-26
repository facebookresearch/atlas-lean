# GRAPH THICKNESS 2 as a decision problem

The decision problem GRAPH THICKNESS 2 accepts a bitstring $x$ exactly when $x$ decodes, under
the canonical bitstring encoding of its instances, to an instance $(n, E)$ such that the [GRAPH
THICKNESS instance](with-bound.md) $(n, E, 2)$ is
[well-formed](../acyclic-coloring/well-formed.md) and
[feasible](../graph-thickness/graph-thickness-feasible.md): the edges can be assigned to
two possibly empty layers, each spanning a planar subgraph. It rejects every bitstring that does not decode to
an instance.
