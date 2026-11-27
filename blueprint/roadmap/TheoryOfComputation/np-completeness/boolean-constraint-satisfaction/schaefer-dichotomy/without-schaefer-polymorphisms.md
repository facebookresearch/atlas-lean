# Without Schaefer polymorphisms, all polymorphisms are projections or negated projections

Let $\Gamma$ be a Boolean constraint language that has none of the six Schaefer polymorphisms. Then every polymorphism of $\Gamma$ is either a projection or a negated projection; in particular all polymorphisms are self-dual, and if additionally some relation of $\Gamma$ is not closed under complementation (some tuple's complement is missing), every polymorphism is a projection. Moreover the failure of each of the six operations is witnessed by a single relation of $\Gamma$, so the conclusion already holds for a sublanguage of at most six relations.

## Proof sketch

$\mathrm{Pol}(\Gamma)$ is a clone; by the four-generator classification, if it contained a non-essentially-unary operation it would contain $\wedge$, $\vee$, majority or minority, contradicting the hypothesis. Constant polymorphisms are excluded, so the remaining essentially unary members are projections and negated projections.

## Depends on

- [Schaefer's six tractable classes](schaefers-six-tractable-classes.md)

## Proof depends on

- [Every Boolean clone is essentially unary or contains AND, OR, majority or minority](../../../../Logic/propositional-logic/boolean-clones-and-cnf-encodings/boolean-clones-and-post-lattice/boolean-clone-four-generator-classification.md)
- [Polymorphisms of a finite structure and its polymorphism clone Pol(A)](../../satisfiability/finite-domain-csp-dichotomy/polymorphism-clone-of-a-finite-structure.md)

## Sources

- H. Chen, "A Rendezvous of Logic, Complexity, and Algebra", SIGACT News 37(4), 85–114, 2006 (extended version ACM Computing Surveys 42(1), 2009): Theorem 5.1 and Lemma 5.2.
