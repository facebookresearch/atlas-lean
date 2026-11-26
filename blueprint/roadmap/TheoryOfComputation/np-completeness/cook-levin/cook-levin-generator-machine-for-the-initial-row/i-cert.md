# Certificate clauses of the initial row (I4)

Let $L$ be a layout with label block size
$A$, $K$ stacks and $g$ symbol codes, let $k_0$ be a stack, let $y = (y_1, \dots, y_r)$ be a list
of natural numbers and let $n, m, T, H$ be natural numbers. For a depth $j$ and a code $x$ write
$C_{j,x} = A + (k_0 H + j)g + x$ for the row-$0$ variable saying that stack $k_0$ holds code $x$
at depth $j$. This is the CNF over $V = (T + 1)(A + KHg)$ variables that has, for
$i = 0, 1, \dots, m - n - 1$ in order (no clauses if $m \le n$), the dense clause over $V$
variables whose literals are the positive literals of the variables $C_{n+i,0}$, $C_{n+i,y_1}$,
$\dots$, $C_{n+i,y_r}$: the cell at depth $n + i$ is empty or holds one of the codes in $y$.

In use, $y$ lists the certificate codes, sorted and distinct.
