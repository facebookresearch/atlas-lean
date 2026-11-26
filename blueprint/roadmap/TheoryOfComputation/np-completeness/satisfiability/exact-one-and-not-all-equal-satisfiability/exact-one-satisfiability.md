# Exact-one satisfiability of a clause formula

Let $\varphi$ be a list of clauses, each a list of literals. An assignment $\sigma$ *one-satisfies* a clause if exactly one literal occurrence of the clause is true under $\sigma$ (repeated occurrences counted with multiplicity), and one-satisfies $\varphi$ if it one-satisfies every clause. $\varphi$ is *exact-one satisfiable* if some assignment one-satisfies it. The *exact-one model count* is the number of assignments of the occurring variables that one-satisfy $\varphi$. Positive exact-one satisfiability with clauses of three literals is the problem 1-in-3-SAT.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [1-IN-3-SAT is NP-complete](../1-in-3-sat/one-in-three-sat-np-complete.md)

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998.
