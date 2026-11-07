# Every top but the last is followed by an end of its row

Let $\varphi$ be a CNF formula
with $m$ clauses and $k$ distinct variables. In Sipser's HAMPATH graph for $\varphi$, clause $j$ is
vertex $j < m$, the top of diamond $i$ is $t_i = m + i(3m + 2)$, and vertex $l \le 3m$ of its row
is $r_{i,l} = t_i + 1 + l$. Let $p$ be a Hamiltonian path of this graph (on the vertices
$0, \dots, t_k$) from $t_0$ to $t_k$ whose detours are normal: for every $j < m$ there is $i < k$
such that $j$ sits in $p$ immediately between $r_{i,3j+1}$ and $r_{i,3j+2}$, in either order. Let
$p'$ be $p$ with the clause vertices deleted. Then for every $i < k$, the top $t_i$ is
immediately followed in $p'$ by $r_{i,0}$ or by $r_{i,3m}$.
