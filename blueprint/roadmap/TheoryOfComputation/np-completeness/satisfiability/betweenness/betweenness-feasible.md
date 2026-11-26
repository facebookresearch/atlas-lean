# BETWEENNESS feasibility

A BETWEENNESS instance $(n, T)$ is feasible when there is an
ordering of the numbers $0, \dots, n-1$ such that for every triple $(a, b, c)$ in $T$, either
$p(a) < p(b) < p(c)$ or $p(c) < p(b) < p(a)$, where $p(m)$ is the position of $m$ in the
ordering, counting from $0$, and $p(m) = n$ when $m$ is not among $0, \dots, n-1$.
