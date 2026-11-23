# Edge relation of a graph

Let $G$ be a graph with vertices $0, \dots, n-1$ and edge table
$t$, a finite list of booleans. For vertices $a, b < n$, there is an edge from $a$ to $b$ exactly
when the entry of $t$ at position $an + b$ (counting from $0$) is true; a position beyond the end
of $t$ counts as false.
