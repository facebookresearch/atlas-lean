# A clause detour returns to its own pair (Sipser's separator argument)

Let $\varphi$ be a
CNF formula with $m$ clauses and $k$ distinct variables, write $T_i = m + i(3m + 2)$ and
$R_{i,l} = T_i + 1 + l$, and let $p$ be a Hamiltonian path from $T_0$ to $T_k$ in the digraph on
the vertices $0, \dots, T_k$ whose arcs are those of Sipser's construction for $\varphi$. Let
$i < k$ and $j < m$, and let $(l_a, l_c)$ be $(3j + 1, 3j + 2)$ or $(3j + 2, 3j + 1)$. If the
clause vertex $j$ comes immediately after $R_{i,l_a}$ in $p$, then every vertex that comes
immediately after $j$ in $p$ is $R_{i,l_c}$.
