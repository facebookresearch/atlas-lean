# Maximum constraint satisfaction problems

Fix a finite domain $D$ and a relation alphabet with semantics $\mathrm{sem}(R) \subseteq D^{r(R)}$. A Max-CSP instance is a list of constraints $(R, (v_1,\dots,v_r))$ on variables $V$; the *score* of an assignment $\sigma : V \to D$ is the number of constraints with $(\sigma v_1,\dots,\sigma v_r) \in \mathrm{sem}(R)$, and the optimum is the maximum score. In a weighted instance each constraint carries a weight in $[0,1]$ and the score sums the weights of satisfied constraints. A CNF formula is a Boolean Max-CSP instance whose relations are clauses.

## Depends on

- [Unsatisfiability value of a CNF formula or CSP instance](unsatisfiability-value.md)
- [BINARY CONSTRAINT SATISFACTION is NP-complete](../../np-completeness/satisfiability/binary-constraint-satisfaction/binary-csp-np-complete.md)

## Sources

- D. P. Williamson and D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011.
- R. O'Donnell, Analysis of Boolean Functions, Cambridge University Press, 2014.
