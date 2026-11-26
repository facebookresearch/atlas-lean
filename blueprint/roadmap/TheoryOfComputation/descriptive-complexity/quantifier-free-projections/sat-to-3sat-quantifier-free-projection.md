# Ordered SAT reduces to 3-SAT by a BIT-free quantifier-free projection

On canonically ordered CNF structures (universe size $n \ge 2$), there is a quantifier-free projection of dimension $5$, using only $\le$, successor, $0$ and $\max$, that maps every CNF structure to a 3-CNF structure that is satisfiable iff the original is. A clause is split along the order of its literals into a chain of width-three clauses with fresh variables indexed by tuples, which ordered structures make possible without $\mathrm{BIT}$.

## Proof sketch

Tuples encode (clause, position, tag) triples; the successor on the universe locates the next literal of each clause, and binary tags in $\{0, \max\}$ select among the gadget roles. Correctness is the usual chain-splitting argument for clauses.

## Depends on

- [First-order and quantifier-free projections](first-order-and-quantifier-free-projections.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Projections compose and are closed under identity](projections-compose.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
- N. Immerman, Descriptive Complexity, Springer, 1999.
