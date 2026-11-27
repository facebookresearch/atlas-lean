# Finite-domain constraint satisfaction problems

Fix a finite nonempty domain $D$ and a relation alphabet with interpretations $\mathrm{sem}(R) \subseteq D^{r}$ (evaluated at the length $r$ of each scope). A CSP instance over variables $V$ is a finite list of constraints $(R, (v_1,\dots,v_r))$; an assignment $\sigma : V \to D$ satisfies it if $(\sigma v_1,\dots,\sigma v_r) \in \mathrm{sem}(R)$ for every constraint. Relabelling variables along an injective map preserves satisfiability, and evaluation depends only on the values of the occurring variables.

## Depends on

- [Boolean constraint languages and CSP(Γ)](../../boolean-constraint-satisfaction/polymorphisms-of-boolean-relations/boolean-constraint-languages.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, Parameterized Algorithms, Springer, 2015.
