# Bipartiteness and acyclicity are not first-order definable

There is no first-order sentence in the language of graphs that holds in exactly the bipartite (2-colorable) finite simple graphs, and none that holds in exactly the acyclic finite simple graphs.

## Proof sketch

On a linear order of size $n$, a definable cycle (successor plus a wrap-around edge) is bipartite iff $n$ is even; the step-two graph (each element joined to the element two above it, and the second element to the last) is acyclic iff $n$ is odd, for $n \ge 5$: for odd $n$ it is a single path, for even $n$ the odd elements form a cycle. Both graphs are defined by first-order formulas over $\le$, so a defining sentence would pull back to a sentence over $\le$ holding in the linear orders of all large even (respectively odd) sizes and no large sizes of the other parity, while first-order definable classes of finite linear orders are finite or cofinite. (Derived.) The same argument shows that both statements remain true when only graphs with at least $t$ vertices are considered, for any fixed $t$.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)

## Proof depends on

- [Graphs defined by a first-order formula](graphs-defined-by-a-formula.md)
- [First-order definable classes of finite linear orders are finite or cofinite](../ehrenfeucht-fraisse-games/even-not-definable-on-linear-orders.md)

## Sources

- V. Tannen, Friendly Logics, Lecture Notes 5, University of Pennsylvania, CIS 682, Fall 2015, Section 1 (bipartiteness and acyclicity listed among the properties that are not FO definable over finite simple graphs).
- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
