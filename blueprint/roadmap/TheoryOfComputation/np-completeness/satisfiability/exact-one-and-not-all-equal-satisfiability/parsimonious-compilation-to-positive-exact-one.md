# Parsimonious compilation of 3-CNF to positive exact-one 3-clauses

There is a polynomial-time map sending every CNF formula $\varphi$ whose clauses have at most three literals to a formula $\psi$ whose clauses are positive (no negated literals) and contain exactly three literals, such that the number of assignments of the variables of $\varphi$ satisfying $\varphi$ equals the exact-one model count of $\psi$. Each source clause yields a bounded number of output clauses, the occurrence count of every source variable is preserved, and every newly introduced variable occurs at most three times. Consequently counting solutions of positive 1-in-3-SAT is $\#\mathsf{P}$-complete, and positive 1-in-3-SAT is NP-complete.

## Proof sketch

Replace each clause by the four-clause parsimonious disjunction gadget of Hunt, Marathe, Radhakrishnan and Stearns (padding short clauses with uniquely forced false variables), then replace every negative literal occurrence by a fresh positive proxy $y$ tied to its variable $z$ by the clause $(z, y, a)$ with $a$ forced to $0$ by the positive gadget $(a,d,e),(a,e,f),(d,e,f)$, whose unique exact-one model is $e=1$, $a=d=f=0$. Each gadget has exactly one auxiliary extension per satisfying source assignment, so counts multiply by one. Hardness of counting follows because counting models of CNF formulas with at most three literals per clause is $\#\mathsf{P}$-complete, and NP-hardness because 3-SAT is NP-complete.

## Depends on

- [Exact-one satisfiability of a clause formula](exact-one-satisfiability.md)
- [Model count of a CNF formula](../../../../Logic/propositional-logic/model-count-preserving-cnf-transformations/model-count.md)
- [$\#P$-complete functions](../../../complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)

## Proof depends on

- [Parsimonious exact-one gadget for a three-literal disjunction](parsimonious-exact-one-disjunction-gadget.md)
- [3SAT is NP-complete](../3-satisfiability/sat3-dec-np-complete.md)
- [Counting SAT is #P-complete](../../../counting-complexity/counting-satisfiability-sat/count-sat-sharp-p-complete.md)

## Sources

- H. B. Hunt III, M. V. Marathe, V. Radhakrishnan and R. E. Stearns, "The Complexity of Planar Counting Problems", SIAM Journal on Computing 27(4), 1142–1167, 1998, Lemma 3.6 and Theorem 3.8.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978 (NP-completeness of 1-in-3-SAT; that reduction is not parsimonious).
