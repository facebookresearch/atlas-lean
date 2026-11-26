# Graph of a weighted edge list

For a natural number $n$ and a list $L$ of quintuples $(u, v, d_0, d_1, d_2)$ of natural numbers, the graph of $L$ on $n$ vertices is the simple graph on $\{0, \dots, n-1\}$ in which distinct vertices $i$ and $j$ are adjacent exactly when $(i, j, d_0, d_1, d_2)$ or $(j, i, d_0, d_1, d_2)$ belongs to $L$ for some weights $d_0, d_1, d_2$. The weights are ignored, loops are dropped, and entries with an endpoint at least $n$ contribute no edge.
