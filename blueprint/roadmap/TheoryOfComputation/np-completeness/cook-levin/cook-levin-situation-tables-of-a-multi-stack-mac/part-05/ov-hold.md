# Overflow cells of the next row hold the table value

Let $E$ be an encoding of a machine
$M$ with $K$ stacks and window depth $d$, and let $a$ be an assignment satisfying the cell-shift
clause family of $E$'s layout and tables $\mathrm{sa}$, $\mathrm{pl}$, $\mathrm{cn}$,
$\mathrm{pu}$ for $E$'s number of situations and bounds $T$ and $H$. Write $X[t, b]$ and
$C[t, k, j, x]$ for the label/state and cell variables at height $H$. Let $t < T$, let $c$ be a
configuration of $M$ all of whose stack symbols have codes, suppose $d \le H$, let $i$ be the
situation index of $c$, and suppose $X[t + 1, \mathrm{sa}(i)]$ is true under $a$. Then for every
$k < K$ and every $j$ with
$H - \max(\mathrm{pl}(i, k), \mathrm{cn}(i, k)) + \mathrm{pl}(i, k) \le j < H$, the variable
$C[t + 1, k, j, x]$ is true under $a$, where $x$ is the value at $(k, j)$ of the table-driven row
update at height $H$ of the cells of $c$ for situation $i$. Subtraction is truncated at zero.

At these depths the table-driven row update is $0$, the empty cell.
