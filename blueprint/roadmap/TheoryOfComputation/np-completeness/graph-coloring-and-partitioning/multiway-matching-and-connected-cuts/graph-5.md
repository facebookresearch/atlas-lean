# Unweighted graph of a list of weighted edges

For a MULTICUT instance with $n$ vertices $0, \dots, n-1$ and a supplied list $T$ of weighted edges $(u, v, w)$, this is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $u$ and $v$ are adjacent when $(u, v, w)$ or $(v, u, w)$ is in $T$ for some weight $w$. Loops and records with an endpoint at least $n$ contribute no edge. The graph depends only on $T$, not on the edges stored in the instance: for the empty list $T$ it is edgeless.
