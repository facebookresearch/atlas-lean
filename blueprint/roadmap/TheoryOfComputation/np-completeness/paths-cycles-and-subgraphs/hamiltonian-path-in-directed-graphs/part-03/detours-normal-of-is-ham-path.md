# Hamiltonian paths of Sipser's graph have normal detours

Let $\varphi$ be a CNF formula
with $m$ clauses and $k$ distinct variables, and write $T_i = m + i(3m + 2)$ and
$R_{i,l} = T_i + 1 + l$ for the top and the row vertices of diamond $i$. Every Hamiltonian path
from $T_0$ to $T_k$ in the digraph on the vertices $0, \dots, T_k$ whose arcs are those of
Sipser's construction for $\varphi$ has normal detours: for every clause $j < m$ there is $i < k$
such that $R_{i,3j+1}, j, R_{i,3j+2}$ or $R_{i,3j+2}, j, R_{i,3j+1}$ occur in this order as
consecutive vertices of the path.
