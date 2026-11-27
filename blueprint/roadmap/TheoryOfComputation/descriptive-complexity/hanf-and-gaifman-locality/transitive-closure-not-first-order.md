# Transitive closure and reachability are not first-order definable

There is no first-order formula $\varphi(x, y)$ over a binary relation $E$ such that on every finite structure $\varphi$ defines the transitive closure of $E$, and none defining its reflexive–transitive closure; likewise no formula defines $s$–$t$ reachability on all finite directed graphs. Indeed a formula of quantifier rank $n$ already fails on every sufficiently long directed path.

## Proof sketch

In a long directed path, the pairs $(a, b)$ and $(b, a)$ for $a, b$ far from each other and from the ends have isomorphic neighborhoods of the Gaifman radius, but exactly one of them is in the transitive closure; Gaifman locality gives a contradiction. (Derived.) With the Gaifman radius $r = (3^{n+1}-1)/2$ of rank-$n$ formulas, every directed path with at least $4r+3 = 2\cdot 3^{n+1}+1$ elements suffices.

## Depends on

- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)
- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)

## Proof depends on

- [Gaifman locality of first-order formulas](gaifman-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- V. Tannen, Friendly Logics, Lecture Notes 5, University of Pennsylvania, CIS 682, Fall 2015, Section 1 (reachability in finite digraphs is not FO definable).
