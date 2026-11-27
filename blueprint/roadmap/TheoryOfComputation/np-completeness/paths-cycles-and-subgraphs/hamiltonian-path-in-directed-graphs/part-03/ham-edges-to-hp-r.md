# In-neighbours of a row vertex in Sipser's graph

Let $\varphi$ be a CNF formula with $m$
clauses, and write $T_i = m + i(3m + 2)$ and $R_{i,l} = T_i + 1 + l$. Let $i$ and $l \le 3m$ be
natural numbers, and let $(v, R_{i,l})$ be an arc of Sipser's construction for $\varphi$. Then
$l < 3m$ and $v = R_{i,l+1}$; or $0 < l$ and $v = R_{i,l-1}$; or $l \in \{0, 3m\}$ and
$v = T_i$; or $v < m$ and $l \in \{3v + 1, 3v + 2\}$.
