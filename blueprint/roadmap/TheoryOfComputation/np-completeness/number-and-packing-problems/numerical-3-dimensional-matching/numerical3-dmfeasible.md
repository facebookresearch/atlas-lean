# Feasible numerical 3-dimensional matching instances

Let $(A, B, C, t)$ be an instance
and let $n$ be the length of $A$, with lists indexed from $0$. The instance is feasible when
there are permutations $p$ and $q$ of the numbers $0$ through $n-1$ such that
$A_j + B_{p(j)} + C_{q(j)} = t$ for every $j < n$, where an entry of $B$ or $C$ at an index past
the end of its list counts as $0$.
