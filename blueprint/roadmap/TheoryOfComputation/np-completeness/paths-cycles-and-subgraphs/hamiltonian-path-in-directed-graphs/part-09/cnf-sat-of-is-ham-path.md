# Backward direction of SAT ≤ HAMPATH for paths with normal detours

Let $\varphi$ be a CNF
formula with $m$ clauses and $k$ distinct variables. In Sipser's HAMPATH graph for $\varphi$, clause
$j$ is vertex $j < m$, the top of diamond $i$ is $t_i = m + i(3m + 2)$, and vertex $l \le 3m$ of
its row is $r_{i,l} = t_i + 1 + l$. If $p$ is a Hamiltonian path of this graph (on the vertices
$0, \dots, t_k$) from $t_0$ to $t_k$ whose detours are normal, that is, for every $j < m$ there is
$i < k$ such that $j$ sits in $p$ immediately between $r_{i,3j+1}$ and $r_{i,3j+2}$, in either
order, then $\varphi$ is satisfiable.

The satisfying assignment makes the variable of diamond $i$ true iff row $i$ is traversed from
left to right.
