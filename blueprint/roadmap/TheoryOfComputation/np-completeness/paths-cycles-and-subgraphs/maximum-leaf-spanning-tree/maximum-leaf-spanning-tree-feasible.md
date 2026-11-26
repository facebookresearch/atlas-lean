# Feasible MAXIMUM LEAF SPANNING TREE instances

An instance $(n, es, K)$ of MAXIMUM LEAF
SPANNING TREE is feasible when there are a sublist $T$ of $es$ (a list obtained from $es$ by
deleting entries) with no repeated entries and exactly $n - 1$ entries, and a set $L$ of at least
$K$ vertices in $\{0, \dots, n - 1\}$, such that the simple graph on $\{0, \dots, n - 1\}$ in
which distinct vertices $i$ and $j$ are adjacent when $(i, j)$ or $(j, i)$ is an entry of $T$ is
connected, and each vertex in $L$ is an endpoint of exactly one entry of $T$.
