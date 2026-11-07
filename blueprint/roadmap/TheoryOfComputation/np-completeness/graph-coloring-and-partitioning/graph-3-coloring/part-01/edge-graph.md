# Graph of an edge list

For a natural number $n$ and a list $es$ of pairs of natural
numbers, the graph of $es$ on $n$ vertices is the simple graph on $\{0, \dots, n-1\}$ in which
distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ belongs to $es$. Loops are
dropped, and pairs with an endpoint at least $n$ contribute no edge.
