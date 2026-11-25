# Classification of the arcs of Sipser's graph

Let $\varphi$ be a CNF formula with $m$
clauses and $k$ distinct variables, and write $T_i = m + i(3m + 2)$ and $R_{i,l} = T_i + 1 + l$.
If $(u, v)$ is an arc of Sipser's construction for $\varphi$, then there is $i < k$ such that one
of the following holds: $u = T_i$ and $v \in \{R_{i,0}, R_{i,3m}\}$; or
$u \in \{R_{i,0}, R_{i,3m}\}$ and $v = T_{i+1}$; or there is $l < 3m$ with
$(u, v) = (R_{i,l}, R_{i,l+1})$ or $(u, v) = (R_{i,l+1}, R_{i,l})$; or there is $j < m$ with
$u \in \{R_{i,3j+1}, R_{i,3j+2}\}$ and $v = j$, or with $u = j$ and
$v \in \{R_{i,3j+1}, R_{i,3j+2}\}$.

The last case does not record whether the detour comes from a positive or a negative literal.
