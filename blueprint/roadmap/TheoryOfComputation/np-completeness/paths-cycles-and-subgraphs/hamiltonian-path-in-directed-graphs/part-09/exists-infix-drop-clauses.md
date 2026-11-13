# Every vertex of the contracted path except its end has a successor

Let $\varphi$ be a CNF
formula with $m$ clauses and $k$ distinct variables. In Sipser's HAMPATH graph for $\varphi$, clause
$j$ is vertex $j < m$ and the top of diamond $i$ is $t_i = m + i(3m + 2)$. Let $p$ be a
Hamiltonian path of this graph (on the vertices $0, \dots, t_k$) from $t_0$ to $t_k$, and let $p'$
be $p$ with the clause vertices deleted. Then every vertex $v \ne t_k$ of $p'$ is immediately
followed in $p'$ by some vertex $w$.
