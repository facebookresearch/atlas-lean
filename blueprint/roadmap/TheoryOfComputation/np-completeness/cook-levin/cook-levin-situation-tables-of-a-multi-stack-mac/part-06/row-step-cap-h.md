# One-step invariant at the stack cap

Fix an encoding $E$ of a machine $M$ with $K$ stacks,
window depth $d$ and $N$ situations, natural numbers $m$, $T$, $t$ with $t < T$, an assignment
$a$ and an input list $s$ of length at most $m$. Let $H = m + (T + 1)d + 1$ be the stack cap and
let $c_t$ be the configuration at time $t$ of the idle-extended run of $M$ from the start
configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If $c_t$ is tracked in row $t$, then $c_{t+1}$ is tracked in row $t + 1$.
