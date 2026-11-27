# Ordered SAT reduces to independent set, clique and vertex cover by quantifier-free projections

On canonically ordered structures, there is a quantifier-free projection of dimension $4$ (over $\le$, successor, $0$, $\max$) from SAT to IndependentSet: vertices are tuples $(\mathrm{role}, c, x, s)$ encoding literal occurrences and padding, edges join complementary occurrences and occurrences in the same clause, and the size relation selects one vertex per clause. Composing with the pairwise equivalences gives quantifier-free projections from SAT to Clique and to VertexCover. Unlike the unordered case, the endpoint constants make the reduction correct on all structures of size at least two.

## Proof sketch

Karp's occurrence-graph construction realized with numeric guards: a satisfying assignment picks one true occurrence per clause, an independent set of the required size; conversely such a set picks consistent true literals.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Ordered independent set, clique and vertex cover are pairwise qfp-equivalent](independent-set-clique-vertex-cover-qfp-equivalent.md)
- [Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility](../first-order-projections/projection-reducibility-is-a-preorder.md)

## Sources

- R. M. Karp, "Reducibility among Combinatorial Problems", in Complexity of Computer Computations, Plenum Press, 85–103, 1972.
- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
- N. Immerman, Descriptive Complexity, Springer, 1999.
