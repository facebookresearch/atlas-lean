# Parity transfer from linear orders to graph properties

If $\delta(x,y)$ is a formula over $\{\le\}$ such that on every finite linear order of size $n \ge t$ the defined graph has a graph property $P$ exactly when $n$ is odd (or exactly when $n$ is even), then $P$ is not first-order definable on finite graphs, even restricted to graphs with at least $t$ vertices. Examples: the *step-two graph*, joining each element to the element two steps above it and the second element to the top element (or analogous end patterns), is connected iff $n$ is odd.

## Proof sketch

A defining sentence for $P$ would pull back along $\delta$ to a sentence over $\le$ defining a parity class of large finite linear orders, contradicting the fact that a first-order definable class of finite linear orders is finite or cofinite.

## Depends on

- [Graphs defined by a first-order formula](graphs-defined-by-a-formula.md)

## Proof depends on

- [First-order definable classes of finite linear orders are finite or cofinite](../ehrenfeucht-fraisse-games/even-not-definable-on-linear-orders.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
