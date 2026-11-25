# Update forcing, real run

Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Fix an input list $s$, let $c_n$ be the configuration
after $n$ steps of the idle-extended run of $M$ from the initial configuration on $s$, let
$T, t \in \mathbb{N}$ with $t < T$, and suppose every stack of $c_t$ has length at most $H - d$.
Let the assignment $a$ satisfy the transition clause family of $L$ with the current-label table
$\mathrm{la}$, the next-label table $\mathrm{na}$ and the window table $\mathrm{wa}$ of $E$, for
$T$, $H$ and the number $N$ of situations. If $X[t, \kappa(c_t)]$ is true under $a$ and
$C[t, k, j, \gamma_{c_t}(k, j)]$ is true under $a$ for all $k < K$ and $j < H$, then the variable
$X[t + 1, \kappa(c_{t+1})]$ is true under $a$.
