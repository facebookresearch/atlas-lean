# Overflow cells of the next row on a real run

Let $E$ be an encoding of a machine $M$ with
$K$ stacks and window depth $d$, let $s$ be an input, and let $c_t$ be the configuration at step
$t$ of the idle-extended run of $M$ from the initial configuration on input $s$. Let $a$ be an
assignment satisfying the cell-shift clause family of $E$'s layout and tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ for $E$'s number of situations and bounds $T$ and $H$,
and write $X[t, b]$ and $C[t, k, j, x]$ for the label/state and cell variables at height $H$.
Suppose $t < T$, every stack of $c_t$ has length at most $H - d$, $d \le H$, and
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$, where $i$ is the situation index of $c_t$. Then for
every $k < K$ and every $j$ with
$H - \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) + \mathrm{pl}(i, k) \le j < H$, the variable
$C[t + 1, k, j, x]$ is true under $a$, where $x$ is the code of the cell of stack number $k$ at
depth $j$ from the top in $c_{t+1}$ ($0$ if that cell is empty). Subtraction is truncated at
zero.
