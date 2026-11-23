# A separator is next to each of its row neighbours on a Hamiltonian path

Let $\varphi$ be
a CNF formula with $m$ clauses and $k$ distinct variables, write $T_i = m + i(3m + 2)$ and
$R_{i,l} = T_i + 1 + l$, and let $p$ be a Hamiltonian path from $T_0$ to $T_k$ in the digraph on
the vertices $0, \dots, T_k$ whose arcs are those of Sipser's construction for $\varphi$. Let
$i < k$, let $l \le 3m$ be a multiple of $3$, and let $l' \le 3m$ satisfy $l' = l + 1$ or
$l' + 1 = l$. Then $R_{i,l'}$ comes immediately before or immediately after $R_{i,l}$ in $p$.
