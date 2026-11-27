# Ordered ESO sentences ground to SAT by quantifier-free projections

Let $\Phi = \exists R_1 \cdots R_m\, \varphi$ be an existential second-order sentence over $\sigma$ together with the strict order $<$. Then the ordered query defined by $\Phi$ reduces to SAT by a quantifier-free projection (without $\mathrm{BIT}$): the projection builds a CNF structure whose variables are the tuples of the relation variables and of Tseitin-style subformula instances of $\varphi$, and whose clauses express the first-order matrix locally. Consequently SAT is complete for $\mathrm{NP}$ under quantifier-free projections on ordered structures, as are 3-SAT, IndependentSet, Clique, VertexCover and 3-colorability; all six are therefore also NP-complete under logspace reductions, and each ordered version is polynomial-time interreducible with its usual string version.

## Proof sketch

Put $\varphi$ in prenex form, introduce a propositional variable for each ground instance of each subformula and of each relation-variable atom, and emit the defining clauses for each instance; all index arithmetic stays within $\le$, successor and endpoints. NP-completeness then follows from Fagin's theorem and the qfp reductions out of SAT, and completeness under logspace reductions from the logspace computability of first-order reductions. Converting between a structure's binary encoding and the usual string encoding of a formula or graph takes polynomial time.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [Existential second-order definable graph classes](../fagin-s-theorem/fagin-esodefinable.md)
- [Binary encoding of finite relational structures](../finite-structures-and-definability/binary-encoding-of-finite-structures.md)

## Proof depends on

- [Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility](../first-order-projections/projection-reducibility-is-a-preorder.md)
- [Ordered SAT reduces to 3-SAT by a BIT-free quantifier-free projection](sat-to-3sat-quantifier-free-projection.md)
- [Ordered SAT reduces to independent set, clique and vertex cover by quantifier-free projections](sat-to-independent-set-quantifier-free-projection.md)
- [Ordered SAT reduces to 3-colorability by a quantifier-free projection](sat-to-3col-quantifier-free-projection.md)
- [Fagin's theorem: NP is existential second-order logic](../fagin-s-theorem/fagin.md)
- [First-order reductions are computable in logarithmic space](../first-order-interpretations-and-reductions/first-order-reductions-logspace-computable.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
- N. Immerman, Descriptive Complexity, Springer, 1999.
- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
- R. Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", in Complexity of Computation, SIAM-AMS Proceedings 7, 43–73, 1974.
