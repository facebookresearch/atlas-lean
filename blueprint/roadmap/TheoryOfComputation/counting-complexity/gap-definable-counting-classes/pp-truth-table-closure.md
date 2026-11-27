# PP is closed under truth-table reductions; P^PP = P^#P

(Beigel–Reingold–Spielman) $\mathsf{PP}$ is closed under intersection and union. (Fortnow–Reingold) More generally, $\mathsf{PP}$ is closed under polynomial-time truth-table reductions, in particular under intersections and unions of polynomially many $\mathsf{PP}$ languages indexed by the input, and even under constant-round truth-table reductions. Moreover $\mathsf{P}^{\mathsf{PP}}=\mathsf{P}^{\#\mathsf{P}}$, since one bit of a shifted $\#\mathsf{P}$ count answers a $\mathsf{PP}$ query and binary search with $\mathsf{PP}$ queries recovers $\#\mathsf{P}$ values.

## Proof sketch

Represent the sign of a gap by a low-degree rational function (Newman's approximation of the sign function) to combine several PP predicates into one gap whose sign is the Boolean combination; the needed polynomials have $\mathsf{GapP}$-computable coefficients.

## Depends on

- [Probabilistic polynomial time with unbounded error](../../complexity-classes/time-and-space-complexity-classes/pp.md)
- [Polynomial time with a #P oracle](../../complexity-classes/time-and-space-complexity-classes/pwith-sharp-p.md)
- [Polynomial-time truth-table, bounded and Turing reductions](../../complexity-classes/structural-complexity/reducibilities-and-isomorphism/truth-table-reductions.md)

## Proof depends on

- [Closure properties of GapP](gapp-closure.md)
- [MAJSAT is PP-complete](../unbounded-error-probabilistic-time-pp/majsat-pp-complete.md)

## Sources

- Richard Beigel, Nick Reingold and Daniel A. Spielman, "PP Is Closed under Intersection", Journal of Computer and System Sciences 50(2), 1995.
- Lance Fortnow and Nick Reingold, "PP Is Closed under Truth-Table Reductions", Information and Computation 124(1), 1996, Theorem 5.4.
- Lance Fortnow, "Counting Complexity", Complexity Theory Retrospective II, 1997, Theorem 4.14.
