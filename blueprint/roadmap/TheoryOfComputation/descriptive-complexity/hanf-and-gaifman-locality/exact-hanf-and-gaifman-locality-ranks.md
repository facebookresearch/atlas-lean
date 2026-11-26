# Exact Hanf and Gaifman locality ranks

The radii in the locality theorems can be improved to their exact values on finite structures: (1) in a finite structure, tuples with isomorphic $(2^n - 1)$-neighborhoods are $n$-equivalent, so every formula of quantifier rank $n$ is Gaifman-local with radius $2^n - 1$; (2) Hanf equivalence at radius $2^{n-1} - 1$ implies $n$-equivalence, so the Hanf locality rank of rank-$n$ formulas is at most $2^{n-1} - 1$. Both bounds are optimal: there are rank-$n$ formulas (expressing distance properties along paths) that are not local at radius $2^n - 2$, respectively not Hanf-local at radius $2^{n-1} - 2$.

## Proof sketch

Refine the Duplicator strategy: track, with $j$ rounds left, a neighborhood radius of $2^j - 1$ around the pebbles, which halves (rather than thirds) after each move because a new pebble either falls within distance $2^j$ of old ones or far away; optimality comes from paths with loops at prescribed distances.

## Depends on

- [Hanf equivalence](hanf-equivalence.md)
- [Gaifman graphs, distance and neighborhoods](gaifman-graphs-and-neighborhoods.md)

## Proof depends on

- [Hanf locality of first-order logic](hanf-locality.md)
- [Gaifman locality of first-order formulas](gaifman-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
