# The accept family of a layout

Let $L$ be a layout with label block size $A$, $K$ stacks
and $g$ symbol codes, let $n_1, a, k_1, e, T, H$ be natural numbers, $W = A + K H g$ and
$V = (T + 1) W$. The accept family is the CNF formula over $V$ variables made of, first, for each
$u < n_1$ in increasing order, the clause whose only literal is the label variable $X[T, u]$
(variable $T W + u$), positive if $u = a$ and negative otherwise; then, for each $x < g$ in
increasing order, the clause whose only literal is the top-cell variable $C[T, k_1, 0, x]$ of
stack $k_1$ (variable $T W + A + k_1 H g + x$), positive if $x = e$ and negative otherwise. Each
clause is a dense row of $V$ slots: the slot of its variable holds the literal and every other
slot is empty (all slots are empty if the variable is at least $V$).
