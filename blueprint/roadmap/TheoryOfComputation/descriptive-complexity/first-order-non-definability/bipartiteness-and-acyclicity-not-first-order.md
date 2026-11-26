# Bipartiteness and acyclicity are not first-order definable

There is no first-order sentence in the language of graphs that holds in exactly the bipartite (2-colorable) finite simple graphs, and none that holds in exactly the acyclic finite simple graphs. Both statements remain true when only graphs with at least $t$ vertices are considered, for any fixed $t$.

## Proof sketch

On a linear order of size $n$, a definable cycle (successor plus a wrap-around edge) is bipartite iff $n$ is even; a definable graph built from step-two edges with endpoints joined is acyclic iff $n$ is even. Apply parity transfer.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)

## Proof depends on

- [Parity transfer from linear orders to graph properties](parity-transfer-from-linear-orders.md)
- [Connectivity is not first-order definable on finite graphs](../../../ComputerScience/databases/query-language-expressiveness/connectivity-is-not-first-order-definable-on-finite-graphs.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
