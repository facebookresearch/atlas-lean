# ESO-definable classes reduce to SAT by order-free interpretations

Let $\sigma$ be relational and $K$ an ESO-definable class of finite $\sigma$-structures that contains the empty structure. Then $K$ reduces to the class of satisfiable CNF structures by an order-free first-order (tagged, quantifier-free) interpretation. Without order, a linear order on the universe can be guessed existentially, so a class of unordered structures defined by an ESO sentence using a built-in linear order in an order-invariant way is ESO-definable without the order.

## Proof sketch

Ground the prenex first-order matrix: tagged copies of tuples serve as propositional variables for ground atoms of relation variables and for subformula instances, and quantifier-free formulas emit the defining clauses. A guessed strict linear order is ESO-definable as a further relation variable.

## Depends on

- [Relational second-order logic on finite structures](relational-second-order-logic.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Pullback of formulas along interpretations](../first-order-interpretations-and-reductions/pullback-along-interpretations.md)
- [First-order reductions preserve definability](../first-order-interpretations-and-reductions/first-order-reductions-preserve-definability.md)

## Sources

- R. Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", in Complexity of Computation, SIAM-AMS Proceedings 7, 43–73, 1974.
- N. Immerman, Descriptive Complexity, Springer, 1999.
