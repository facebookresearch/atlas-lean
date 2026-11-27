# In-neighbours of a row vertex outside the clause vertices

Let $\varphi$ be a CNF formula
with $m$ clauses. In Sipser's HAMPATH graph for $\varphi$, clause $j$ is vertex $j < m$, the top of
diamond $i$ is $t_i = m + i(3m + 2)$, and $\rho_b(i, l)$ denotes vertex $l$ of the row of diamond
$i$ counted from the left end if $b$ is true and from the right end if $b$ is false. Let
$l \le 3m$ and $u \ge m$. If $(u, \rho_b(i, l))$ is an arc of the graph, then $l > 0$ and
$u = \rho_b(i, l - 1)$, or $l < 3m$ and $u = \rho_b(i, l + 1)$, or $l \in \{0, 3m\}$ and
$u = t_i$.
