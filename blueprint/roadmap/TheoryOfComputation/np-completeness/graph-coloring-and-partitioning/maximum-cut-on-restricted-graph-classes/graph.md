# Graph of a max-cut instance on cographs

The graph of an instance of MAX CUT for cographs with edge weights 1 and 2: the simple graph on
the vertices $0, \dots, n - 1$, where $n$ is the vertex count of the instance, in which two
distinct vertices $u$ and $v$ are adjacent exactly when the weighted edge list $E$ of the
instance contains an entry $(u, v, w)$ or $(v, u, w)$, whatever its weight $w$. Loops $(u, u)$
add no edge, and an entry with an endpoint outside $0, \dots, n - 1$ contributes nothing.
