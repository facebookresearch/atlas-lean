# Lexicographic order, successor and BIT on tuples are definable

For every dimension $k \ge 1$, identify $\{0,\dots,n-1\}^k$ with $\{0,\dots,n^k - 1\}$ by lexicographic rank (first coordinate most significant). Then the order, the successor relation and equality on $k$-tuples ordered lexicographically are quantifier-free definable from the corresponding relations on single elements, and the constants $0$ and $n^k - 1$ on $k$-tuples are the $k$-tuples $(0,\dots,0)$ and $(n-1,\dots,n-1)$; for example, for $k = 2$ the successor is

$$
s\big((x_1,x_2),(y_1,y_2)\big) \iff \big(x_1 = y_1 \wedge s(x_2,y_2)\big) \vee \big(x_2 = n-1 \wedge y_2 = 0 \wedge s(x_1,y_1)\big).
$$

$\mathrm{BIT}$ on $k$-tuples (bit $j$ of the rank of $\bar x$, for $j$ given as the rank of a tuple) cannot in general be replaced by a quantifier-free formula, but it is first-order definable from $\le$ and $\mathrm{BIT}$.

## Proof sketch

Lexicographic comparison is a finite disjunction over the first differing coordinate; the successor increments the last non-maximal coordinate and resets later ones. For BIT, represent ranks as fixed-length words in a radix that is a power of two and convert bases with the definable word arithmetic.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)

## Proof depends on

- [Multiplication is first-order definable from order and BIT](multiplication-definable-from-bit.md)

## Sources

- N. Immerman and S. Landau, "The Complexity of Iterated Multiplication", Information and Computation 116(1), 103–116, 1995, Section 3, remarks after Definition 3.3 (quantifier-free formulas on $k$-tuples ordered lexicographically; "BIT on tuples is definable in FO (with BIT)").
- N. Immerman, Descriptive Complexity, Springer, 1999.
