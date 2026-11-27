# Boolean gap-2CSP is decidable in polynomial time

Every promise problem on binary constraint graphs over the alphabet $\{0,1\}$ whose yes-instances are satisfiable and whose no-instances are unsatisfiable lies in $\mathrm{PromiseP}$; there is a single deterministic polynomial-time algorithm for all of them. In particular the gap problem $\mathrm{gapCSP}^{\{0,1\}}_\tau$ (satisfiable versus at least a $\tau(n)$ fraction violated) is in $\mathrm{PromiseP}$ for every positive threshold function $\tau$, which shows that a constant-gap PCP over a binary alphabet cannot have two queries with perfect completeness unless $\mathrm{P} = \mathrm{NP}$.

## Proof sketch

Each binary constraint on Boolean labels is a set of allowed pairs, expressible as a conjunction of clauses of width at most two on the two label bits. The graph is satisfiable iff the resulting 2-CNF is, and 2-SAT is decidable in polynomial time by the implication-graph algorithm.

## Depends on

- [2CSP instances](../dinur-s-gap-amplification/cspinstance.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)

## Proof depends on

- [2-SAT characterization](../../../Logic/propositional-logic/2-satisfiability/cnf-sat-iff-of-is-two-cnf.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
