# In-range shift forcing (L1)

Let $L$ be a layout with $K$ stacks and $g$ symbol codes,
let $sa$, $pl$, $cn$, $pu$ be situation tables and $N, T, H \in \mathbb{N}$, and let $a$ be an
assignment satisfying the cell-shift clause family of $L$ with these tables and bounds $N$, $T$,
$H$. Call a variable true when its index is less than the length of $a$ and $a$ is true there.
Write $S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$ and $C[t, k, j, x]$ for the
cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$). Let
$t < T$, $i < N$, $k < K$, $x < g$ and $u < H - \max(pl(i, k), cn(i, k))$, with truncated
subtraction. If $S[t, i]$ and $C[t, k, u + cn(i, k), x]$ are true, then
$C[t + 1, k, u + pl(i, k), x]$ is true.
