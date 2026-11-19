# Output of the stopping Moore iteration

Let $M$ be a DFA over a finite alphabet with
finitely many states, and write $R$ for one round of Moore's refinement. For every
$n \in \mathbb{N}$ and every set $E$ of pairs of states of $M$, there is $k \le n$ such that the
stopping Moore iteration from $E$ with budget $n$ returns $R^k(E)$, and if $k < n$ then $R^k(E)$
is a fixed point of $R$, that is, $R(R^k(E)) = R^k(E)$.
