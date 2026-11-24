# Run tracking from the init obligation

Fix an encoding $E$ of a machine $M$ with $K$
stacks, window depth $d$ and $N$ situations, lists $x$ and $Y$ of input symbols, natural numbers
$m$ and $T$, and an assignment $a$, and let $H = m + (T + 1)d + 1$ be the stack cap.
Suppose $a$ satisfies the transition clause families of the layout of $E$ with tables
$(\mathrm{la}, \mathrm{na}, \mathrm{wa})$ and $(\mathrm{la}, \mathrm{sa}, \mathrm{wa})$ and the
cell-shift clause family with tables $(\mathrm{sa}, \mathrm{pl}, \mathrm{cn}, \mathrm{pu})$, all
for time bound $T$, height $H$ and $N$ situations.
Say that a configuration $c$ is tracked in row $t$ when, in the layout of $E$ at height $H$, the
literal of the (label, state) code of $c$ in row $t$ is true under $a$ and, for every stack number
$k < K$ and depth $j < H$, the literal of the cell code of $c$ at stack $k$ and depth $j$ in row
$t$ is true under $a$.
If the init obligation holds for $a$, $x$, $Y$, $m$ and $T$, then there is a list $y$ of input
symbols, each occurring in $Y$, such that the concatenation $xy$ has length at most $m$ and, for
every $t \le T$, the configuration at time $t$ of the idle-extended run of $M$ from the start
configuration on $xy$ is tracked in row $t$.
