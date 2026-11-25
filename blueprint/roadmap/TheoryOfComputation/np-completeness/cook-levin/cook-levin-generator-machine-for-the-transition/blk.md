# Encoded transition clauses of one time step

Given a layout $L$, tables
$la, na : \mathbb{N} \to \mathbb{N}$ and
$wa : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \mathbb{N}$, and natural numbers $N$, $T$, $H$,
$t$, this is the bit string obtained by concatenating, for $i = 0, 1, \dots, N - 1$ in this order,
the encoding of the dense clause over $V$ variables whose literals are the literals of clause
$(t, i)$, where $V$ is the number of variables of $L$ for $T$ and $H$.
