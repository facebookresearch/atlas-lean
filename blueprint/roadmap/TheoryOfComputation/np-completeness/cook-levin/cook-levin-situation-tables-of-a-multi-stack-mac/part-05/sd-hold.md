# L2 (S-definition, positive)

Let $E$ be an encoding of the machine $M$ with $K$ stacks and
layout $L$, let $d$ be the window depth of $M$, let $H \in \mathbb{N}$ with $d \le H$, let $W$ be
the row width of $L$ at height $H$, and write $X[t, x] = tW + x$ for the label/state variables and
$C[t, k, j, x]$ for the cell variable of row $t$, stack $k$, depth $j$ and symbol code $x$. For a
configuration $c$ write $\kappa(c)$ for its (label, state) code and $\gamma_c(k, j)$ for the code
of its cell at stack $k$ and depth $j$. Let $T, t \in \mathbb{N}$ with $t < T$, and let the
assignment $a$ satisfy the transition clause family of $L$ for $T$, $H$ and the number $N$ of
situations, with the current-label table $\mathrm{la}$ and the window table $\mathrm{wa}$ of $E$,
and with the table $\mathrm{sa}$ of $E$ (where $\mathrm{sa}(i)$ is the position of the variable of
situation $i$ in the label/state block) in place of the next-label table. Let $c$ be a good
configuration with situation index $i$ such that $X[t, \kappa(c)]$ is true under $a$ and
$C[t, k, j, \gamma_c(k, j)]$ is true under $a$ for all $k < K$ and $j < H$. Then the variable
$X[t + 1, \mathrm{sa}(i)]$ is true under $a$.
