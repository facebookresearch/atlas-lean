# Positive core of the shift step (L2⁺)

Let $M$ be a finite multi-stack Turing machine and
$E$ an encoding of $M$ with $K$ numbered stacks, tables $sa$, $pl$, $cn$, $pu$ and $N$ situations,
let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment satisfying the cell-shift
clause family of the layout of $E$ with these tables and bounds $N$, $T$, $H$. Call a variable
true when its index is less than the length of $a$ and $a$ is true there. Write $S[t, i]$ for the
label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for the cell variable of row $t$,
stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and $\mathrm{cell}(c, k, j)$ for
the code at depth $j$ of the stack numbered $k$ of a configuration $c$ ($0$ if there is none).
Let $c$ be a configuration that is good for $E$ (every stack symbol lies in the effective
alphabet of its stack), with situation index $i$. Suppose that
$C[t, k', j', \mathrm{cell}(c, k', j')]$ is true for all $k' < K$ and $j' < H$, and that
$S[t, i]$ is true. Then for every $k < K$ and every $j$ with
$pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$ (truncated subtraction), the variable
$C[t + 1, k, j, R(k, j)]$ is true, where $R$ is the table-driven row update at height $H$ of the
cells of $c$ for situation $i$.
