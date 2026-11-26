# Feasible directed disjoint paths instances

Let $(n, A, P)$ be an instance of DIRECTED
DISJOINT PATHS whose list of source-target pairs is
$P = ((s_0, t_0), \dots, (s_{k-1}, t_{k-1}))$. The instance is feasible when there are lists
$\pi_0, \dots, \pi_{k-1}$ of natural numbers such that, for every $p < k$, the list $\pi_p$ is
nonempty, has no repeated entries, has first entry $s_p$ and last entry $t_p$, has all its
entries less than $n$, and every two consecutive entries $u, v$ of $\pi_p$ form an arc $(u, v)$
occurring in $A$; and such that, for all distinct $p, q < k$, no $v < n$ is an entry of both
$\pi_p$ and $\pi_q$.
