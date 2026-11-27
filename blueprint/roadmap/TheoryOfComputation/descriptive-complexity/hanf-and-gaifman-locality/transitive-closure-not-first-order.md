# Transitive closure and reachability are not first-order definable

There is no first-order formula $\varphi(x, y)$ over a binary relation $E$ such that on every finite structure $\varphi$ defines the transitive closure of $E$, and none defining its reflexive–transitive closure; likewise no formula defines $s$–$t$ reachability on all finite directed graphs. Indeed if $\varphi$ has quantifier rank $n$, it already fails on every directed path with at least $4r+3 = 2\cdot 3^{n+1}+1$ elements, where $r=(3^{n+1}-1)/2$.

## Proof sketch

In a long directed path, the pairs $(a, b)$ and $(b, a)$ for $a, b$ far from each other and from the ends have isomorphic neighborhoods of the Gaifman radius, but exactly one of them is in the transitive closure; Gaifman locality gives a contradiction.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)

## Proof depends on

- [Gaifman locality of first-order formulas](gaifman-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
