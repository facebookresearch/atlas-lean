# The tail of a clause chain

Write $y_v$ for the variable with index $2^{v+1} + 1$ (the
$v$-th fresh variable), $\ell'$ for a literal $\ell$ whose variable index $n$ is replaced by $2n$
with the same polarity, and $z \ominus j$ for $\max(z - j, 0)$. Given literals
$\ell_1, \dots, \ell_m$ and a natural number $z$, the result is the empty formula if $m = 0$, and
otherwise the $m$ clauses $(\neg y_{z \ominus (i - 1)} \lor \ell_i' \lor y_{z \ominus i})$ for
$i = 1, \dots, m - 1$, followed by $(\neg y_{z \ominus (m - 1)} \lor \ell_m')$.

Here $z$ is the fresh number of the variable asserted by the clause before the tail; fresh
numbers decrease along the chain.
