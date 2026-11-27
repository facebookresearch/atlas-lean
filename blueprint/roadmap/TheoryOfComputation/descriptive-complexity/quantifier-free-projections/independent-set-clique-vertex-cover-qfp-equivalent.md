# Ordered independent set, clique and vertex cover are pairwise qfp-equivalent

On canonically ordered sized-graph structures, the queries IndependentSet, Clique and VertexCover are pairwise reducible to each other by quantifier-free projections: IndependentSet and Clique reduce to each other by complementing the off-diagonal edge relation (a one-dimensional projection), and IndependentSet and VertexCover reduce to each other by complementing the size relation, since $S$ is independent iff $V \setminus S$ is a vertex cover.

## Proof sketch

The loop-free complement of the edge relation is a projection selecting $\bot$ on the diagonal and the negated input edge elsewhere; the complement of the size relation has cardinality $n - k$. Check that the target sizes match.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility](../first-order-projections/projection-reducibility-is-a-preorder.md)

## Sources

- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
- N. Immerman, Descriptive Complexity, Springer, 1999.
- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
