# Vertex sets meeting a mode's pair condition

For a mode $m$, a number $n$, a list of
pair bits and a set $s$ of vertices in $\{0, \dots, n - 1\}$, the set $s$ meets the condition
of $m$ when for all vertices $i < j$ the pair condition
$\mathrm{ok}_m(b_{ij}, [i \in s], [j \in s])$ holds, where $[i \in s]$ says whether $i$ is
chosen and $b_{ij}$ is the bit of the pair $\{i, j\}$: listing the pairs $i' < j' < n$ in
encoding order (rows $i'$ ascending, within a row $j'$ descending), the $t$-th bit of the list
belongs to the $t$-th pair, and $b_{ij}$ is false if the list has no bit for $\{i, j\}$.
