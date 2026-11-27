# Håstad: gap MAX-E3SAT with imperfect completeness is NP-hard beyond 7/8

For all $\delta, \varepsilon > 0$ with $7/8 + \varepsilon < 1 - \delta$, it is NP-hard to distinguish exact-3-CNF formulas (three distinct variables per clause) in which some assignment satisfies at least a $1 - \delta$ fraction of the clauses from those in which every assignment satisfies at most a $7/8 + \varepsilon$ fraction. Hence every $\rho > 7/8$ approximation for MAX-E3SAT in polynomial time implies $\mathrm{P} = \mathrm{NP}$, matching the $7/8$ achieved by a random assignment or by Johnson's algorithm.

## Proof sketch

Compose the NP-hardness of $\mathrm{GapE3LIN}_2(1 - 4\delta, 1/2 + 4\varepsilon)$ with the four-clause gadget: a $1/2 + \varepsilon'$ fraction of satisfied equations becomes a $1 - (1/2 - \varepsilon')/4 = 7/8 + \varepsilon'/4$ fraction of satisfied clauses.

## Depends on

- [The MAX-3SAT objective](../approximability-of-max-3sat/max3-satval.md)
- [NP-complete decision problems](../../complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Håstad: MAX-E3LIN-2 is NP-hard to approximate beyond 1/2](hastad-max-e3lin2-inapproximability.md)
- [Four-clause gadget from 3-variable XOR constraints to exact 3-CNF](four-clause-xor-to-e3cnf-gadget.md)

## Sources

- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 2001.
