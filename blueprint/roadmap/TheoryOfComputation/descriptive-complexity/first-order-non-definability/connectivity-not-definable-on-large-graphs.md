# Connectivity is not first-order definable even on large graphs

For every $t \in \mathbb{N}$ there is no first-order sentence in the language of graphs that holds in exactly the connected finite simple graphs with at least $t$ vertices, among graphs with at least $t$ vertices. The step-two graph of a finite linear order of size $n$ is connected iff $n$ is odd.

## Proof sketch

The step-two graph on $\{0,\dots,n-1\}$ with an edge between the second and the last element is a single path when $n$ is odd, and the disjoint union of a cycle (on the odd elements) and a path (on the even elements) when $n$ is even; apply parity transfer.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)

## Proof depends on

- [Graphs defined by a first-order formula](graphs-defined-by-a-formula.md)
- [First-order definable classes of finite linear orders are finite or cofinite](../ehrenfeucht-fraisse-games/even-not-definable-on-linear-orders.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
