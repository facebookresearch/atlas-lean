# Exact MAX-SAT distributions from threshold counts

For a CNF with $m$ clauses, let $T_q$ be the number of assignments satisfying at least $q$ clauses, $0\le q\le m+1$. Then the number of assignments satisfying exactly $q$ clauses is $T_q-T_{q+1}$, and the maximum number of simultaneously satisfiable clauses equals $|\{q\le m : T_q>0\}|-1$. Hence any threshold model counter gives the full score histogram and the MAX-SAT optimum with $m+2$ calls, preserving subexponential running times.

## Proof sketch

$T_q$ is nonincreasing with $T_0=2^n$ and $T_{m+1}=0$; adjacent differences telescope and the positive values are exactly $q=0,\dots,\mathrm{OPT}$.

## Depends on

- [MAXIMUM SATISFIABILITY as a decision problem](../../np-completeness/satisfiability/maximum-satisfiability/max-sat-dec.md)
- [Counting satisfying assignments of a CNF formula](../../counting-complexity/counting-satisfiability-sat/count-sat-fun.md)

## Sources

- Ryan Williams, "A New Algorithm for Optimal 2-Constraint Satisfaction and Its Implications", Theoretical Computer Science 348(2–3), 2005.
