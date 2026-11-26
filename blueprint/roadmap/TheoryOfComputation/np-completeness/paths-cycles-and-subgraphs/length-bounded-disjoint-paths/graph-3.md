# Graph of an instance of MINIMUM MAXIMUM DISJOINT CONNECTING PATHS

The graph of an instance of MINIMUM MAXIMUM DISJOINT CONNECTING PATHS: the simple graph on the
vertices $0, \dots, n - 1$, where $n$ is the vertex count of the instance, in which two distinct
vertices $u$ and $v$ are adjacent exactly when the weighted edge list $E$ of the instance
contains an entry $(u, v, \ell)$ or $(v, u, \ell)$, whatever its weight $\ell$. Loops $(u, u)$
add no edge, and an entry with an endpoint outside $0, \dots, n - 1$ contributes nothing. It is the [graph of an edge list](../../graph-coloring-and-partitioning/graph-3-coloring/part-01/edge-graph.md) on these vertices and pairs.
