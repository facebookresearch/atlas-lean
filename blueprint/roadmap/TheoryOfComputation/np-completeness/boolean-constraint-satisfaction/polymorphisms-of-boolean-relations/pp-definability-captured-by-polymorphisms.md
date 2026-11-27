# Geiger / Bodnarčuk et al.: pp-definability is captured by polymorphisms

Let $\Gamma$ be a Boolean constraint language and $R$ a nonempty Boolean relation. Then $R$ is pp-definable from $\Gamma$ (with equality) if and only if every polymorphism of $\Gamma$ preserves $R$. If moreover the coordinate columns of $R$ are pairwise distinct, an equality-free pp-definition exists: the canonical conjunction whose variables are the Boolean columns indexed by the tuples of $R$ and whose constraints are all atoms of $\Gamma$ satisfied pointwise, with the coordinates of $R$ as free variables. Consequently, if $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Delta)$ then $\mathrm{CSP}(\Delta)$ reduces to $\mathrm{CSP}(\Gamma)$ in polynomial time.

## Proof sketch

Polymorphisms preserve pp-definable relations. For the converse take the canonical conjunction on columns indexed by the tuples of $R$: its satisfying assignments are exactly the polymorphisms of $\Gamma$ of arity $|R|$, and projecting them onto the coordinate columns gives $R$ precisely when these polymorphisms preserve $R$.

## Depends on

- [Primitive-positive definitions and gadgets](primitive-positive-definitions.md)
- [Polymorphisms of relations](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/boolean-clones-and-post-lattice/polymorphisms-of-relations.md)

## Proof depends on

- [Closure properties of polymorphisms](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/boolean-clones-and-post-lattice/closure-properties-of-polymorphisms.md)

## Sources

- D. Geiger, "Closed Systems of Functions and Predicates", Pacific Journal of Mathematics 27(1), 95–100, 1968.
- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009).
- P. Jeavons, D. Cohen and M. Gyssens, "Closure Properties of Constraints", Journal of the ACM 44(4), 527–548, 1997.
