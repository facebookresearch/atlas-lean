# Arcs from a row into a clause vertex

Let $\varphi$ be a CNF formula with $m$ clauses
$C_0, \dots, C_{m-1}$, and let $x_i$ be the $i$-th of its distinct variables (variable $0$ if
$\varphi$ has at most $i$ distinct variables). In Sipser's HAMPATH graph for $\varphi$, clause $j$
is vertex $j$, and $r_{i,l}$ denotes vertex $l$ of the row of diamond $i$. If $l \le 3m$, $j < m$
and $(r_{i,l}, j)$ is an arc of the graph, then either $l = 3j + 1$ and the literal $x_i$ occurs
in $C_j$, or $l = 3j + 2$ and the literal $\neg x_i$ occurs in $C_j$.
