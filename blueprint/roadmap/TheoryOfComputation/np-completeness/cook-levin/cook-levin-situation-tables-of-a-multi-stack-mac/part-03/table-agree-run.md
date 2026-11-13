# The table-driven step along a run

Fix an encoding $E$ of a finite TM2 machine $M$, with
$K$ stacks, $N$ situations and window depth $d$, a natural number $H$, an input list $s$ and a
time $t$. For each time $u$ let $c_u$ be the configuration at time $u$ of the idle-extended run
of $M$ from the initial configuration of $M$ on input $s$, and let $i$ be the situation index of
$c_t$. If every stack of $c_t$ has length at most $H \mathbin{\dot{-}} d$ (truncated subtraction),
then $i < N$; the label/state code of situation $i$ is the combined (label, state) code of $c_t$;
for all $k < K$ and $j < d$ the window symbol code of situation $i$ on stack $k$ at depth $j$ is
the cell code of $c_t$ on stack number $k$ at depth $j$; the combined (label, state) code of
$c_{t+1}$ is the next label/state code after situation $i$; and for all $k < K$ and $j < H$ the
cell code of $c_{t+1}$ on stack number $k$ at depth $j$ is the value at $(k, j)$ of the
table-driven row update with height $H$ and situation $i$ applied to the cell codes of $c_t$.

Unlike the single-step version, no alphabet hypothesis is needed: every symbol on a stack of such
a run lies in the effective alphabet of $E$.
