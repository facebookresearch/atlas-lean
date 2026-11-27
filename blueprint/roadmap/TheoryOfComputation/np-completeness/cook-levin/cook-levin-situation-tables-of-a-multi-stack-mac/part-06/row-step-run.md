# One-step invariant

Fix an encoding $E$ of a machine $M$ with $K$ stacks, window depth $d$
and $N$ situations, natural numbers $T$, $H$, $t$ with $t < T$ and $d \le H$, an assignment $a$
and an input list $s$, and let $c_t$ be the configuration at time $t$ of the idle-extended run of
$M$ from the start configuration on $s$.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If every stack of $c_t$ has length at most $H - d$ and $c_t$ is tracked in row $t$, then
$c_{t+1}$ is tracked in row $t + 1$.
