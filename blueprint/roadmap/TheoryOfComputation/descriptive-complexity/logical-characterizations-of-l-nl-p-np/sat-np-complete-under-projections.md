# Immerman: SAT is NP-complete under BIT-free quantifier-free projections

Encode CNF formulas as ordered structures (clauses, variables, positive and negative occurrence relations). Then for every query $A$ on ordered structures the following are equivalent: (i) the encoded language of $A$ is in $\mathsf{NP}$; (ii) $A$ is definable in existential second-order logic; (iii) $A$ reduces to SAT by a BIT-free quantifier-free projection; (iv) $A$ reduces to SAT by a first-order reduction. In particular ordered SAT is $\mathsf{NP}$-complete under quantifier-free projections.

## Proof sketch

(i)⇔(ii) is Fagin's theorem on ordered structures. For (ii)⇒(iii), put an ESO sentence in the form $\exists\bar R\,\forall\bar x\,\psi$ with $\psi$ quantifier-free CNF in the $R$-atoms, and ground it: variables are the tuples of the $R$'s and clauses are indexed by $\bar x$, each literal determined by one input literal. (iv)⇒(i) because NP is closed under logspace reductions.

## Depends on

- [First-order interpretations, first-order reductions and quantifier-free projections](first-order-reductions.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [Existential second-order definable graph classes](../fagin-s-theorem/fagin-esodefinable.md)

## Proof depends on

- [Fagin's theorem: NP is existential second-order logic](../fagin-s-theorem/fagin.md)
- [Cook–Levin theorem: SAT is NP-complete](../../np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- Neil Immerman, "Descriptive Complexity", Springer, 1999.
- Neil Immerman and Susan Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 1995.
- Ronald Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", Complexity of Computation, 1974.
