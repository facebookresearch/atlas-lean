# Vertex pairs in encoding order for one more vertex

For a natural number $m$, write
$P(m)$ for the list of pairs $(i, j)$ of natural numbers with $i < j < m$, ordered by $i$
ascending and, for each $i$, by $j$ descending. Then for every natural number $n$, $P(n + 1)$ is
the list $(0, n), (0, n - 1), \dots, (0, 1)$ (empty when $n = 0$) followed by the pairs
$(i + 1, j + 1)$ for the pairs $(i, j)$ of $P(n)$, in the order of $P(n)$.
