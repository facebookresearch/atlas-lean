# The chain of clauses replacing one clause

Write $y_v$ for the variable with index
$2^{v+1} + 1$ (the $v$-th fresh variable) and $\ell'$ for a literal $\ell$ whose variable index $n$
is replaced by $2n$, with the same polarity. Given a clause $C$ and a natural number $u$, the
empty clause is replaced by the empty clause alone, a one-literal clause $\ell_1$ by the clause
$\ell_1'$, and a clause $\ell_1 \lor \dots \lor \ell_k$ with $k \ge 2$ by the $k$ clauses
$(\ell_1' \lor y_{u+k-2})$, then $(\neg y_{u+k-i} \lor \ell_i' \lor y_{u+k-i-1})$ for
$i = 2, \dots, k - 1$, then $(\neg y_u \lor \ell_k')$. A clause of length $k \ge 2$ thus uses
the fresh numbers $u$ to $u + k - 2$.
