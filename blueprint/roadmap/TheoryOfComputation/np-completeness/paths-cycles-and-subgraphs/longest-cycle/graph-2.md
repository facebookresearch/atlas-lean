# Graph

The graph of an instance of LONGEST CIRCUIT: the simple graph on the vertices $0, \dots, n - 1$,
where $n$ is the vertex count of the instance, in which two distinct vertices $u$ and $v$ are
adjacent exactly when the weighted edge list $E$ of the instance contains an entry
$(u, v, \ell)$ or $(v, u, \ell)$, whatever its weight $\ell$. Loops $(u, u)$ add no edge, and an
entry with an endpoint outside $0, \dots, n - 1$ contributes nothing.
