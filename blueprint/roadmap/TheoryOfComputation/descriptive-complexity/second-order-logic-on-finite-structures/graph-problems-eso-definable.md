# Colorability, independent set, clique and vertex cover are ESO-definable

For every $c \ge 1$, $c$-colorability of finite graphs is defined by the ESO sentence $\exists C_1 \cdots C_c\, \big(\forall x \bigvee_i C_i x \wedge \forall x \forall y\, (E x y \to \bigwedge_i \neg(C_i x \wedge C_i y))\big)$. The sized-graph problems IndependentSet, Clique and VertexCover are ESO-definable by guessing a set $S$ and a bijection $F$ between $S$ and the size relation and checking the first-order condition on $S$. These give direct (Fagin-style) NP membership certificates.

## Proof sketch

An expansion satisfying the matrix is exactly a coloring (resp. a set of the right size with the required property); conversely each solution yields such an expansion.

## Depends on

- [Relational second-order logic on finite structures](relational-second-order-logic.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Fagin's theorem: NP is existential second-order logic](../fagin-s-theorem/fagin.md)

## Sources

- R. Fagin, "Generalized First-Order Spectra and Polynomial-Time Recognizable Sets", in Complexity of Computation, SIAM-AMS Proceedings 7, 43–73, 1974.
- N. Immerman, Descriptive Complexity, Springer, 1999.
