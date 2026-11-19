# At-most-one clauses of the first rows of a cell

For natural numbers $V$, $B$ and $y$,
write $p_i$ for the variable with index $i$. This is the CNF formula listing, for
$y' = 0, 1, \dots, y - 1$ in turn and within each for $x = 0, 1, \dots, y' - 1$ in turn, the
dense clause over $V$ variables built from the literals $\lnot p_{B + x}$ and $\lnot p_{B + y'}$:
its slot $i < V$ holds the literal on $p_i$ if there is one and is empty otherwise.
