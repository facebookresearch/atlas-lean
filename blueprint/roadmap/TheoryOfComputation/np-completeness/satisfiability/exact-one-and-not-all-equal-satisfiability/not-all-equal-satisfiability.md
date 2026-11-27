# Not-all-equal satisfiability

A clause $\ell_1 \vee \dots \vee \ell_k$ is *not-all-equal satisfied* by an assignment $\sigma$ if at least one literal is true and at least one literal is false under $\sigma$; in particular empty and singleton clauses are never NAE-satisfied. A CNF formula is NAE-satisfiable if some assignment NAE-satisfies every clause. Since complementing every variable maps NAE-satisfying assignments to NAE-satisfying assignments, the NAE-models of a formula over at least one variable come in complementary pairs.

## Depends on

- [CNF formula](../../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [NOT-ALL-EQUAL 3-SAT is NP-complete](../not-all-equal-3-sat/nae-three-sat-np-complete.md)

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
- M. R. Garey and D. S. Johnson, Computers and Intractability: A Guide to the Theory of NP-Completeness, W. H. Freeman, 1979.
