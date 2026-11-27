# Unsatisfiability value of a CNF formula or CSP instance

For a CNF formula $\varphi$ with $m \ge 1$ clauses (counted with multiplicity), let $\mathrm{unsat}(\varphi, \sigma)$ be the number of clauses falsified by the assignment $\sigma$. The *unsatisfiability value* is $\mathrm{uval}(\varphi) = \min_\sigma \mathrm{unsat}(\varphi,\sigma)/m$, with $\mathrm{uval}(\varphi) = 0$ for the empty formula. It vanishes exactly on satisfiable formulas, and $1 - \mathrm{uval}(\varphi)$ is the optimal MAX-SAT value. The same definition applies to a CSP instance under a relation semantics, counting violated constraints.

## Depends on

- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)
- [The MAX-3SAT objective](../approximability-of-max-3sat/max3-satval.md)
- [Finite-domain constraint satisfaction problems](../../np-completeness/satisfiability/constraint-satisfaction-encodings/finite-domain-constraint-satisfaction.md)
- [Maximum constraint satisfaction problems](maximum-constraint-satisfaction-problems.md)

## Sources

- D. P. Williamson and D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
