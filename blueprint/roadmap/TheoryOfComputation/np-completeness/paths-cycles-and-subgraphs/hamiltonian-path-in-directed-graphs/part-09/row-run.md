# A row entered at one end is run to the other end

Let $\varphi$ be a CNF formula with
$m$ clauses and $n$ distinct variables. For $k \le n$ let $t_k = m + k(3m + 2)$ be the top of
diamond $k$, and for $k < n$ let row $k$ consist of the vertices $t_k + 1 + l$ with
$0 \le l \le 3m$; its left end is $t_k + 1$ and its right end is $t_k + 1 + 3m$. Let $p$ be a
Hamiltonian path from $t_0$ to $t_n$ in Sipser's digraph for $\varphi$ on the vertices
$0, \dots, t_n$ whose clause detours are normal: every clause vertex $j < m$ occurs in $p$
immediately between the vertices $t_k + 3j + 2$ and $t_k + 3j + 3$ of some row $k < n$, in
either order. Let $q$ be $p$ with the clause vertices $0, \dots, m - 1$ deleted. Let $i < n$,
let $e$ be an end of row $i$, and for $0 \le l \le 3m$ let $r_l$ be the $l$-th vertex of row $i$
counted from $e$, that is $r_l = t_i + 1 + l$ if $e$ is the left end and $r_l = t_i + 1 + 3m - l$
if $e$ is the right end. If the top $t_i$ is immediately followed by $r_0$ in $q$, then for every
$l < 3m$ the vertex $r_l$ is immediately followed by $r_{l+1}$ in $q$.
