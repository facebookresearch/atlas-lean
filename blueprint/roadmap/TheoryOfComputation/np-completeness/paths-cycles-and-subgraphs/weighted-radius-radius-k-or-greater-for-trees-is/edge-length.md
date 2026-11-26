# Edge lengths from a list of lengths

Let $(n, E, C, K)$ be an instance with edge list $E = (e_0, e_1, \dots)$, and let $w = (w_0, w_1, \dots)$ be a list of natural numbers, read as giving the $j$-th listed edge $e_j$ the length $w_j$. For an unordered pair $s = \{a, b\}$ of vertices, the length of $s$ is $w_j$ for the least index $j < \min(|E|, |w|)$ such that $e_j = (a, b)$ or $e_j = (b, a)$, and $0$ if there is no such index.
