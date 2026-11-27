# Graph of a multicommodity-flow instance

The graph of an instance $(n, E, P, K)$ is the simple graph on the vertices $0, \dots, n-1$ in which distinct vertices $u$ and $v$ are adjacent when $(u, v, c)$ or $(v, u, c)$ is in $E$ for some capacity $c$; entries with an endpoint at least $n$ contribute no edge.

RURAL POSTMAN uses this same graph of its edge list: distinct $u$ and $v$ below $n$ are adjacent when $(u, v)$ or $(v, u)$ is the endpoint pair of a listed edge, and loops and pairs with an endpoint out of range contribute no edge.
