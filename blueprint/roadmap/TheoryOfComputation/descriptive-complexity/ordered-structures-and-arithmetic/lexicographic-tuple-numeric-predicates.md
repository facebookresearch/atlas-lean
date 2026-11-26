# Lexicographic order, successor and BIT on tuples are definable

For every dimension $k \ge 1$, identify $\{0,\dots,n-1\}^k$ with $\{0,\dots,n^k - 1\}$ by lexicographic rank (first coordinate most significant). Then: the lexicographic order and the constants $0$, $1$, $n^k-1$ on $k$-tuples are quantifier-free definable from $\le$ and the constants; the non-wrapping successor on $k$-tuples is quantifier-free definable from the source successor by a finite carry case distinction; and $\mathrm{BIT}$ on $k$-tuples (bit $j$ of the rank of $\bar x$, for $j$ given as the rank of a tuple) is first-order definable from $\le$ and $\mathrm{BIT}$.

## Proof sketch

Lexicographic comparison is a finite disjunction over the first differing coordinate; the successor increments the last non-maximal coordinate and resets later ones. For BIT, represent ranks as fixed-length words in a radix that is a power of two and convert bases with the definable word arithmetic.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)

## Proof depends on

- [Multiplication is first-order definable from order and BIT](multiplication-definable-from-bit.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
