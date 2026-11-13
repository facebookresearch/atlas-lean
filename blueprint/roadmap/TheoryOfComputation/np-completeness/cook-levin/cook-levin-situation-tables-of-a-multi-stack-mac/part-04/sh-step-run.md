# Exact shift step on a real run (L3)

Let $M$ be a finite multi-stack Turing machine and
$E$ an encoding of $M$ with $K$ numbered stacks, $g$ symbol codes, tables $sa$, $pl$, $cn$, $pu$
and $N$ situations, let $T, H, t \in \mathbb{N}$ with $t < T$, and let $a$ be an assignment
satisfying the cell-shift clause family of the layout of $E$ with these tables and bounds $N$,
$T$, $H$. Call a variable true when its index is less than the length of $a$ and $a$ is true
there. Write $S[t, i]$ for the label/state variable $sa(i)$ of row $t + 1$, $C[t, k, j, x]$ for
the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$ (both at height $H$), and
$\mathrm{cell}(c, k, j)$ for the code at depth $j$ of the stack numbered $k$ of a configuration
$c$ ($0$ if there is none). Fix an input list $s$, let $c_n$ be the configuration after $n$
idle-extended steps of $M$ from the initial configuration on $s$, and let $i$ be the situation
index of $c_t$. Suppose that every stack of $c_t$ has length at most $H - d$, where $d$ is the
window depth of $M$, that for all $k' < K$, $j' < H$ and $x < g$ the variable $C[t, k', j', x]$
is true exactly when $x = \mathrm{cell}(c_t, k', j')$, and that $S[t, i]$ is true. Let $k < K$
and $pl(i, k) \le j < H - \max(pl(i, k), cn(i, k)) + pl(i, k)$, and suppose at most one $x < g$
makes $C[t + 1, k, j, x]$ true. Then for every $x < g$, $C[t + 1, k, j, x]$ is true exactly when
$x = \mathrm{cell}(c_{t+1}, k, j)$. Subtraction is truncated at $0$.

No row is decoded in the proof.
