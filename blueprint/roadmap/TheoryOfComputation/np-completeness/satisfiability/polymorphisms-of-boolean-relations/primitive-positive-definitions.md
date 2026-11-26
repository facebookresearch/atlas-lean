# Primitive-positive definitions and gadgets

A relation $R \subseteq \{0,1\}^k$ is *primitive-positively definable* (pp-definable) from a constraint language $\Gamma$ if there are a conjunction $\Phi(x_1,\dots,x_k, y_1,\dots,y_m)$ of atomic formulas $S(z_1,\dots,z_r)$ with $S \in \Gamma$ and an existential quantification of the auxiliary variables $y$ such that $R = \{(a_1,\dots,a_k) : \exists b\; \Phi(a,b)\}$. A pp-definition is *equality-free* if equality atoms are not used. A pp-definition used as a replacement for constraints of $R$ in an instance, with fresh auxiliary variables per occurrence, is a *gadget*; replacing all $R$-constraints by gadgets preserves satisfiability.

## Depends on

- [Boolean constraint languages and CSP(Γ)](boolean-constraint-languages.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- P. Jeavons, D. Cohen and M. Gyssens, "Closure Properties of Constraints", Journal of the ACM 44(4), 527–548, 1997.
