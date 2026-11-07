# A satisfying choice gives a Hamiltonian path

Let $\varphi$ be a CNF formula with $m$
clauses, let $v_0, \dots, v_{k-1}$ be its distinct variables in the order used by the
construction, let $\sigma$ assign a truth value to every variable, and write
$t_a = m + a(3m + 2)$ for the top of diamond $a$. Let $c : \mathbb{N} \to \mathbb{N}$ be such
that for every $j < m$ we have $c(j) < k$ and clause $j$ of $\varphi$ contains the literal over
$v_{c(j)}$ that $\sigma$ makes true (positive if $\sigma(v_{c(j)})$ is true, negative
otherwise). Then the forward path through the first $k$ diamonds for $c$, with diamond $i$
traversed in direction $\sigma(v_i)$, is a Hamiltonian path from $t_0$ to $t_k$ in the digraph
on the vertices $0, \dots, t_k$ whose arcs are the arcs of the construction for $\varphi$.
