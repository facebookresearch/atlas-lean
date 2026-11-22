# Pushed-fill forcing for a good configuration

Let $E$ be an encoding of the machine $M$
with $K$ stacks and layout $L$, let $H \in \mathbb{N}$, let $W$ be the row width of $L$ at height
$H$, and write $X[t, x] = tW + x$ for the label/state variables and $C[t, k, j, x]$ for the cell
variable of row $t$, stack $k$, depth $j$ and symbol code $x$. Let $T, t \in \mathbb{N}$ with
$t < T$, let the assignment $a$ satisfy the cell-shift family of $E$ (tables $\mathrm{sa}$,
$\mathrm{pl}$, $\mathrm{cn}$, $\mathrm{pu}$ and $N$ situations) for $T$ and $H$, and let $c$ be a
good configuration with situation index $i$ such that $X[t + 1, \mathrm{sa}(i)]$ is true under
$a$. Then for all $k < K$ and $j < \mathrm{pl}(i, k)$ the variable $C[t + 1, k, j, r]$ is true
under $a$, where $r$ is the entry at stack $k$ and depth $j$ of the table-driven row update, at
height $H$ and for situation $i$, of the cell codes of $c$.
