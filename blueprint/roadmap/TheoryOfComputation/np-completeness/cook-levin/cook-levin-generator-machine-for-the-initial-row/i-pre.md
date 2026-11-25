# Row-0 prefix clauses

Let $L$ be a layout with label block size $A$, $K$ stacks and $g$
symbol codes, let $k_0$ be a stack, let $n, m, T, H$ be natural numbers, and write
$z_j = A + (k_0 H + j)g$ for the row-$0$ variable saying that stack $k_0$ holds code $0$ (the
empty cell) at depth $j$. This is the CNF over $V = (T + 1)(A + KHg)$ variables that has, for
$i = 0, 1, \dots, m - n - 1$ in order (no clauses if $m \le n$), the dense clause over $V$
variables whose literals are the negative literal of variable $z_{n+i}$ and the positive literal
of variable $z_{n+i+1}$: an empty cell at depth $n + i$ forces an empty cell at depth
$n + i + 1$.
