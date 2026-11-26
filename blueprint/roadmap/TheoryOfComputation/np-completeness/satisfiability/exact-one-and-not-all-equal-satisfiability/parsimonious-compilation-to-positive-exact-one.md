# Parsimonious compilation of 3-CNF to positive exact-one 3-clauses

There is a polynomial-time map sending every CNF formula $\varphi$ whose clauses have at most three literals to a formula $\psi$ whose clauses are positive (no negated literals) and contain exactly three literals, such that the number of assignments of the variables of $\varphi$ satisfying $\varphi$ equals the exact-one model count of $\psi$. Each source clause yields at most $13 \cdot 13$ output clauses, the occurrence count of every source variable is preserved, and every newly introduced variable occurs at most three times. Consequently counting solutions of positive 1-in-3-SAT is $\#\mathsf{P}$-complete, and positive 1-in-3-SAT is NP-complete.

## Proof sketch

Replace each clause by the four-clause parsimonious disjunction gadget (padding short clauses with uniquely forced false variables), then replace every negative literal occurrence by a fresh positive proxy tied to its variable by the parsimonious complement gadget. Each gadget has exactly one auxiliary extension per satisfying source assignment, so counts multiply by one.

## Depends on

- [Exact-one satisfiability of a clause formula](exact-one-satisfiability.md)
- [Model count of a CNF formula](../../../../Logic/propositional-logic/model-count-preserving-cnf-transformations/model-count.md)

## Proof depends on

- [Parsimonious exact-one gadget for a three-literal disjunction](parsimonious-exact-one-disjunction-gadget.md)
- [1-IN-3-SAT is NP-complete](../1-in-3-sat/one-in-three-sat-np-complete.md)

## Sources

- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
