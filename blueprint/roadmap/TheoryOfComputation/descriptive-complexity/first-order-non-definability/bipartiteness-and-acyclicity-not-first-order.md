# Bipartiteness and acyclicity are not first-order definable

There is no first-order sentence in the language of graphs that holds in exactly the bipartite (2-colorable) finite simple graphs, and none that holds in exactly the acyclic finite simple graphs. Both statements remain true when only graphs with at least $t$ vertices are considered, for any fixed $t$.

## Proof sketch

On a linear order of size $n$, a definable cycle (successor plus a wrap-around edge) is bipartite iff $n$ is even; the step-two graph (each element joined to the element two above it, and the second element to the last) is acyclic iff $n$ is odd, for $n \ge 5$: for odd $n$ it is a single path, for even $n$ the odd elements form a cycle. Apply parity transfer.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)

## Proof depends on

- [Parity transfer from linear orders to graph properties](parity-transfer-from-linear-orders.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
