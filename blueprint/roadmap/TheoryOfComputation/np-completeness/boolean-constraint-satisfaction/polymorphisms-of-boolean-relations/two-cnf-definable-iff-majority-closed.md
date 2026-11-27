# 2-CNF-definable relations are exactly the majority-closed relations

A Boolean relation $R \subseteq \{0,1\}^I$ on a finite coordinate set $I$ is definable by a CNF formula over $I$ whose clauses have width at most two (with no auxiliary variables) if and only if the ternary majority operation is a polymorphism of $R$. Such relations are called *bijunctive*.

## Proof sketch

The median of three assignments satisfying a clause of width at most two satisfies it, since two of the three agree on a true literal. Conversely, a majority-closed relation is determined by its projections onto pairs of coordinates (a tuple whose every two-coordinate projection lies in the projection of $R$ belongs to $R$), and each binary projection is a 2-CNF.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../../satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)
- [2-CNF formulas](../../../../Logic/propositional-logic/2-satisfiability/is-two-cnf.md)

## Sources

- M. Bodirsky, Graph Homomorphisms and Universal Algebra, lecture notes, TU Dresden.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- P. Jeavons, D. Cohen and M. Gyssens, "Closure Properties of Constraints", Journal of the ACM 44(4), 527–548, 1997.
