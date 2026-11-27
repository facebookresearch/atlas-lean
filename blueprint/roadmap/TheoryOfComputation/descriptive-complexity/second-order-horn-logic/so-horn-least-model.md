# SO∃-Horn sentences are decided by the least model

For an SO∃-Horn sentence and a structure $\mathfrak{A}$, the definite clauses define a monotone immediate-consequence operator on tuples of relations; its least fixed point $\mathcal{M}$ is the least model of the definite clauses. The sentence holds in $\mathfrak{A}$ iff no goal clause is violated by $\mathcal{M}$. Consequently model checking a fixed SO∃-Horn sentence is in polynomial time.

## Proof sketch

Models of definite clauses are closed under intersection, so the least model exists and is reached by iterating the consequence operator; goal clauses are preserved downward, so a model exists iff the least one satisfies them.

## Depends on

- [Existential second-order Horn logic](existential-second-order-horn-logic.md)

## Proof depends on

- [Horn satisfiability via the least model](../../../Logic/propositional-logic/horn-satisfiability/satisfies-least-model-iff.md)
- [Least model equals least fixpoint for Datalog](../../../ComputerScience/databases/datalog/least-model-equals-least-fixpoint-for-datalog.md)

## Sources

- E. Grädel, "Capturing Complexity Classes by Fragments of Second-Order Logic", Theoretical Computer Science 101(1), 35–57, 1992.
