# The construction has a Hamiltonian path iff the formula is satisfiable

Let
$\varphi$ be a CNF formula with $m$ clauses and $k$ distinct variables, and let
$t_i = m + i(3m + 2)$ be the top vertex of diamond $i$ in Sipser's construction. The digraph on
the vertices $0, \dots, t_k$ whose arcs are the arcs of the construction for $\varphi$ has a
Hamiltonian path from $t_0$ to $t_k$ if and only if $\varphi$ is satisfiable.
