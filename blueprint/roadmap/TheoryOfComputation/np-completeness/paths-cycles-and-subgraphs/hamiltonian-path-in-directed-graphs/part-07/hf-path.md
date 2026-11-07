# The forward path through the diamonds

Let $m$ and $k$ be natural numbers, let
$c : \mathbb{N} \to \mathbb{N}$ be a map and let $d : \mathbb{N} \to \{\mathrm{true},
\mathrm{false}\}$ give each diamond $i$ a direction $d(i)$. The forward path through the first
$k$ diamonds is the list obtained by concatenating, for $i = 0, 1, \dots, k - 1$ in this order,
the traversal of diamond $i$ for $c$ in direction $d(i)$, and then appending the vertex
$m + k(3m + 2)$, the top of diamond $k$. Here the traversal of diamond $i$ is its top
$m + i(3m + 2)$ followed by its row $r_0, r_1, \dots, r_{3m}$, where
$r_l = m + i(3m + 2) + 1 + l$ and the clause vertex $j$ is inserted right after $r_{3j+1}$ for
every $j < m$ with $c(j) = i$; the row is read left to right if $d(i)$ is true and right to left
otherwise.
