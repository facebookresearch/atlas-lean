# Exact Hanf and Gaifman locality ranks

For a purely relational vocabulary and $n \ge 2$, the radii in the locality theorems can be improved to their exact values on finite structures: (1) in a finite structure, tuples with isomorphic $(2^n - 1)$-neighborhoods are $n$-equivalent, so every formula of quantifier rank $n$ is Gaifman-local with radius $2^n - 1$; (2) Hanf equivalence at radius $2^{n-1} - 1$ implies $n$-equivalence, so the Hanf locality rank of rank-$n$ formulas is at most $2^{n-1} - 1$. Both bounds are optimal: there are rank-$n$ formulas (expressing distance properties along paths) that are not local at radius $2^n - 2$, respectively not Hanf-local at radius $2^{n-1} - 2$.

## Proof sketch

Upper bounds: replace isomorphic neighborhoods of whole tuples by $r$-similarity (a partition of the tuple into blocks with isomorphic $r$-neighborhoods and pairwise distance greater than $r$); Hanf equivalence at radius $r$ extends $2r$-similar tuples to $r$-similar ones by a bijection, so radii halve, rather than shrink by a factor of three, per quantifier. Lower bounds: the rank-$n$ formulas $d_n(x,y)$ saying that $x$ and $y$ are at distance at most $2^n$ (with $d_0 = E$ and $d_{j+1}(x,y) = \exists z\,(d_j(x,z) \wedge d_j(y,z))$) and their relatives.

## Depends on

- [Hanf equivalence](hanf-equivalence.md)
- [Gaifman graphs, distance and neighborhoods](gaifman-graphs-and-neighborhoods.md)
- [Quantifier rank and rank-$n$ equivalence](../finite-structures-and-definability/quantifier-rank.md)

## Proof depends on

- [Hanf locality of first-order logic](hanf-locality.md)
- [Gaifman locality of first-order formulas](gaifman-locality.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004: Exercises 4.10 and 4.11 (exact values $2^{n-1}-1$ and $2^n - 1$ for $n > 1$) and the formulas $d_k$ of Section 4.3.
- L. Libkin, "Logics with Counting and Local Properties", ACM Transactions on Computational Logic 1(1), 33–59, 2000.
