# A Hamiltonian path of Sipser's graph does not cross a diamond through one row end

Let
$\varphi$ be a CNF formula with $m \ge 1$ clauses and $k$ distinct variables, write
$T_i = m + i(3m + 2)$ and $R_{i,l} = T_i + 1 + l$, and let $p$ be a Hamiltonian path from $T_0$
to $T_k$ in the digraph on the vertices $0, \dots, T_k$ whose arcs are those of Sipser's
construction for $\varphi$. For $i < k$ and $l \in \{0, 3m\}$, it is impossible that $R_{i,l}$
comes immediately after $T_i$ in $p$ and $T_{i+1}$ comes immediately after $R_{i,l}$ in $p$.
