# Edge lengths from a list of lengths

Let $(n, E, C, K)$ be an instance with edge list $E = (e_0, e_1, \dots)$, and let $w = (w_0, w_1, \dots)$ be a list of natural numbers, read as giving the $j$-th listed edge $e_j$ the length $w_j$. For any unordered pair $s = \{a, b\}$ of vertices, whether or not it is an edge of the graph, the length of $s$ is $w_j$ for the least index $j < \min(|E|, |w|)$ such that $e_j = (a, b)$ or $e_j = (b, a)$, and $0$ if there is no such index.

No well-formedness is assumed: reversed or repeated entries of $E$ use the first match, a pair that is not an edge may still get a length (for $n = 1$, $E = ((0, 0))$ and $w = (7)$, the pair $\{0, 0\}$ has length $7$), and an edge with no paired entry of $w$ has length $0$. The same function gives the edge lengths for WEIGHTED DIAMETER with diameter $K$ or greater.
