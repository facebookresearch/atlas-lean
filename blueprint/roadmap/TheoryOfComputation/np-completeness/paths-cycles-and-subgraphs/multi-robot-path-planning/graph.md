# Graph

The graph of an instance of MULTI-ROBOT PATH PLANNING with bounded makespan: the simple graph on
the vertices $0, \dots, n - 1$, where $n$ is the vertex count of the instance, in which two
distinct vertices $u$ and $v$ are adjacent exactly when the edge list $E$ of the instance
contains the pair $(u, v)$ or the pair $(v, u)$. Loops $(u, u)$ add no edge, and an entry with
an endpoint outside $0, \dots, n - 1$ contributes nothing.
