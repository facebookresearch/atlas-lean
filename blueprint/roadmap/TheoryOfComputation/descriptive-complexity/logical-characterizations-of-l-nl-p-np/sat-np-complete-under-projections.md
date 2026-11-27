# Immerman: NP is the class of ordered queries reducing to SAT by quantifier-free projections

Encode CNF formulas as ordered structures (clauses, variables, positive and negative occurrence relations). Then for every query $A$ on ordered structures the following are equivalent: (i) the encoded language of $A$ is in $\mathsf{NP}$; (ii) $A$ is definable in existential second-order logic; (iii) $A$ reduces to SAT by a BIT-free quantifier-free projection; (iv) $A$ reduces to SAT by a first-order reduction.

## Proof sketch

(i)⇔(ii) is Fagin's theorem on ordered structures. (ii)⇒(iii) grounds the ESO sentence to a CNF structure by a quantifier-free projection. (iii)⇒(iv) holds because a quantifier-free projection is a first-order reduction. (iv)⇒(i) because NP is closed under logspace reductions.

## Depends on

- [First-order and quantifier-free reductions](../first-order-interpretations-and-reductions/first-order-reductions.md)
- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Existential second-order definable graph classes](../fagin-s-theorem/fagin-esodefinable.md)

## Proof depends on

- [Fagin's theorem: NP is existential second-order logic](../fagin-s-theorem/fagin.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)
- [Ordered ESO sentences ground to SAT by quantifier-free projections](../quantifier-free-projections/eso-grounding-to-sat-quantifier-free-projection.md)
- [First-order reductions are computable in logarithmic space](../first-order-interpretations-and-reductions/first-order-reductions-logspace-computable.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
- Ronald Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", in Complexity of Computation, SIAM-AMS Proceedings 7, 43–73, 1974.
