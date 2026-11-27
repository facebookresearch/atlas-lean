# Ordered SAT reduces to 3-colorability by a quantifier-free projection

On canonically ordered structures, SAT reduces by a quantifier-free projection (over $\le$, successor, $0$, $\max$) to 3-colorability of directed graphs with loops forbidden, and to 3-colorability of simple loopless undirected graphs. The projection lays out the palette triangle, a pair of literal vertices per variable and an OR-gadget chain per clause, ordered along the successor.

## Proof sketch

Standard palette/OR-gadget reduction; the gadget positions are tuples whose roles are selected by quantifier-free numeric guards, and the edge relation of the output is a projection of the input clause relations.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility](../first-order-projections/projection-reducibility-is-a-preorder.md)
- [Order-free first-order reductions between 3-SAT and 3-colorability](../first-order-interpretations-and-reductions/order-free-reductions-3sat-3col.md)

## Sources

- M. R. Garey and D. S. Johnson, Computers and Intractability: A Guide to the Theory of NP-Completeness, W. H. Freeman, 1979.
- M. Sipser, Introduction to the Theory of Computation, 3rd ed., Cengage Learning, 2013.
- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
