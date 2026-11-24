# Adjacency bit of a vertex pair

Let $n$, $i$, $j$ be natural numbers and $b$ a list of
bits. List the pairs $(i', j')$ with $i' < j' < n$ in encoding order ($i'$ ascending and, for
each $i'$, $j'$ descending) and match the $t$-th pair with the $t$-th bit of $b$, for as many
positions as both lists have. The adjacency bit of $\{i, j\}$ is the bit matched with
$(\min(i, j), \max(i, j))$, and false when that pair has no matched bit (for instance when
$i = j$, when $\max(i, j) \ge n$, or when $b$ is too short).
