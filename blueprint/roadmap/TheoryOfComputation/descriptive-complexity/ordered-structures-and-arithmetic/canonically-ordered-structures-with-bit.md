# Canonically ordered structures with BIT

For an input vocabulary $\sigma$ and $n \ge 2$, a *canonically ordered* $\sigma$-structure has universe $\{0,\dots,n-1\}$ expanded by the numeric vocabulary: the order $\le$, the constants $0$, $1$, $\max = n-1$, and the binary predicate $\mathrm{BIT}(x, i)$, true when bit $i$ (least significant first) of the binary expansion of $x$ is $1$. The numeric symbols have their standard meanings and are not part of the input. An *ordered query* is a class of such structures; it is *first-order definable* if one first-order sentence over $\sigma$ plus the numeric vocabulary defines it on all canonically ordered structures. The *encoded language* of an ordered query is the set of binary encodings of the $\sigma$-reducts of its structures. A logic $\mathcal{L}$ *captures* a complexity class $\mathcal{C}$ on ordered structures if the ordered queries definable by $\mathcal{L}$-sentences are exactly those whose encoded languages lie in $\mathcal{C}$.

## Depends on

- [Finite ordered graphs](../immerman-vardi-theorem/ordered-graph.md)
- [Isomorphism-closed classes and first-order definability on finite structures](../finite-structures-and-definability/first-order-definable-classes.md)
- [Binary encoding of finite relational structures](../finite-structures-and-definability/binary-encoding-of-finite-structures.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- D. A. M. Barrington, N. Immerman and H. Straubing, "On Uniformity within NC¹", Journal of Computer and System Sciences 41(3), 274–306, 1990.
