# Affine relations are exactly the minority-closed relations

A Boolean relation $R \subseteq \{0,1\}^I$ on a finite coordinate set $I$ is the solution set of a system of linear equations $\bigoplus_{i \in S} x_i = b$ over $\mathbb{F}_2$ (empty systems and the inconsistent equation $0 = 1$ allowed) if and only if the ternary minority operation $x \oplus y \oplus z$ is a polymorphism of $R$. Consequently $\mathrm{CSP}(\Gamma)$ for affine $\Gamma$ is solvable in polynomial time by Gaussian elimination, after instantiating fixed affine templates of the relations in the constraint scopes.

## Proof sketch

Solution sets of linear systems are cosets, closed under $x \oplus y \oplus z$. Conversely a nonempty minority-closed set is a coset of the linear subspace $\{x \oplus y : x,y \in R\}$, hence the solution set of a linear system.

## Depends on

- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../../satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)
- [Boolean constraint languages and CSP(Γ)](boolean-constraint-languages.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Theorem 4.3.
- T. J. Schaefer, "The Complexity of Satisfiability Problems", Proceedings of the 10th ACM Symposium on Theory of Computing (STOC), 216–226, 1978.
