# One-hot clauses of a cell

For $g, V, B \in \mathbb{N}$, the CNF formula whose first clause
is the at-least-one clause $v_B \lor \dots \lor v_{B+g-1}$ and whose remaining clauses are the
at-most-one clauses $\neg v_{B+x} \lor \neg v_{B+y}$ for $x < y < g$, ordered by $y$ and then by
$x$. Each clause is written densely over the $V$ variables $v_0, \dots, v_{V-1}$; literals on
variables of index at least $V$ are dropped.
