# Edges Graph

The simple graph on the vertices $0, \dots, n - 1$ of a list $L$ of weighted edges $(u, v, w)$:
distinct $u$ and $v$ are adjacent exactly when $L$ contains an entry $(u, v, w)$ or $(v, u, w)$
for some weight $w$. It is the [graph of an edge list](../../graph-coloring-and-partitioning/graph-3-coloring/part-01/edge-graph.md) on these vertices and pairs.

Several problems build their graph this way from a list of triples whose third field (a weight, a length or a class) the conversion ignores, applied to the instance's edge list or, for a candidate forest, to a candidate list.
