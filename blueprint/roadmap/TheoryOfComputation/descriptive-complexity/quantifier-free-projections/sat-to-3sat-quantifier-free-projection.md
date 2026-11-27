# Ordered SAT reduces to 3-SAT by a BIT-free quantifier-free projection

On canonically ordered CNF structures (universe size $n \ge 2$), there is a quantifier-free projection of dimension $5$, using only $\le$, successor, $0$ and $\max$, that maps every CNF structure to a 3-CNF structure that is satisfiable iff the original is. A clause is split along the order of the universe into a chain of width-three clauses with fresh variables indexed by tuples, which ordered structures make possible without $\mathrm{BIT}$.

## Proof sketch

Tuples encode (clause, position, tag) triples; for each clause $c$ a chain variable $y(c,x)$ ("some literal of $c$ at a position up to $x$ is true") is passed from $x$ to its successor, and each link is a short clause containing $y(c,x-1)$, $\neg y(c,x)$ and the literal of $c$ at position $x$ if present (the presence bits $\mathrm{pos}(c,x)$, $\mathrm{neg}(c,x)$ are the projected input literals; a position carrying both a positive and a negative literal uses one more tagged link). Binary tags in $\{0, \max\}$ select among the gadget roles, and a unit clause asserts $y(c,\max)$. No step needs to find the next literal of a clause, so no quantifier is needed. Correctness is the usual chain-splitting argument for clauses.

## Depends on

- [First-order and quantifier-free projections (Immerman-Landau)](../first-order-projections/first-order-and-quantifier-free-projections.md)
- [CNF formulas, graphs and sized graphs as finite structures](../first-order-interpretations-and-reductions/cnf-formulas-and-graphs-as-finite-structures.md)

## Proof depends on

- [Immerman-Landau: first-order and quantifier-free projection reducibilities are preorders refining FO reducibility](../first-order-projections/projection-reducibility-is-a-preorder.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995.
- N. Immerman, Descriptive Complexity, Springer, 1999.
