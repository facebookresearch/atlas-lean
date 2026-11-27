# Schaefer's six tractable classes

A Boolean constraint language $\Gamma$ satisfies *Schaefer's criterion* if at least one of the following holds: (1) every nonempty relation contains the all-zero tuple ($0$-valid: the constant $0$ is a polymorphism); (2) every nonempty relation contains the all-one tuple ($1$-valid: the constant $1$ is a polymorphism); (3) every relation is Horn (closed under $\wedge$); (4) every relation is dual Horn (closed under $\vee$); (5) every relation is bijunctive (closed under majority); (6) every relation is affine (closed under minority). Equivalently, $\Gamma$ has one of the six polymorphisms $0$, $1$, $\wedge$, $\vee$, $\mathrm{maj}$, $x \oplus y \oplus z$. Schaefer's original conditions (a) and (b) require every relation to contain the constant tuple; the two readings differ only when $\Gamma$ contains the empty relation, and the dichotomy theorem is correct only for the reading above (an instance using the empty relation is trivially unsatisfiable, and otherwise the constant assignment works).

## Depends on

- [Boolean constraint languages and CSP(Γ)](../polymorphisms-of-boolean-relations/boolean-constraint-languages.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../../satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)

## Sources

- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978, Theorem 2.1 (weakly negative = Horn, weakly positive = dual Horn).
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Theorem 3.20.
