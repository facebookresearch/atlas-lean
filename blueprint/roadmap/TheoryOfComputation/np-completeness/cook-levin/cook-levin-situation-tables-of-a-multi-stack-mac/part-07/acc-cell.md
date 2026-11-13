# Accept-cell clauses

Let $E$ be an encoding of a finite stack machine $M$ with output
stack $k_1$, $g$ symbol codes and stack numbering $\kappa$, let $\alpha$ be a symbol of stack $k_1$
with code $e$, and let $T, H \in \mathbb{N}$. In the layout of $E$ at height $H$, let $W$ be the
row width, $V = (T + 1)W$ the number of variables, and $C[t, k, j, x]$ the variable for stack $k$,
depth $j$ and symbol code $x$ at time $t$. The accept-cell clauses are the CNF formula listing,
for each $x < g$ in increasing order, the dense clause over $V$ variables built from the single
literal $C[T, \kappa(k_1), 0, x]$ if $x = e$ and $\neg C[T, \kappa(k_1), 0, x]$ otherwise.
