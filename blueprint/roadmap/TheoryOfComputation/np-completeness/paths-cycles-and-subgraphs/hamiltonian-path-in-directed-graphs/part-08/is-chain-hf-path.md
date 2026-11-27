# Chain condition for the forward path

Let $R$ be a relation on $\mathbb{N}$, let $m$ and
$k$ be natural numbers, $c : \mathbb{N} \to \mathbb{N}$ a map and $d : \mathbb{N} \to
\{\mathrm{true}, \mathrm{false}\}$ a choice of directions, and write $t_a = m + a(3m + 2)$ for
the top of diamond $a$. If for every $i < k$ the traversal of diamond $i$ for $c$ in direction
$d(i)$, followed by $t_{i+1}$, is a chain for $R$ (every entry is related by $R$ to the next
one), then the forward path through the first $k$ diamonds for $c$ and $d$ is a chain for
$R$.
