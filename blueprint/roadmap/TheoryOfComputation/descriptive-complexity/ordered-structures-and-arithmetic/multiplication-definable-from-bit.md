# Multiplication is first-order definable from order and BIT

There is a first-order formula $\mathrm{TIMES}(x, y, z)$ over $\{\le, \mathrm{BIT}\}$ such that on every canonically ordered universe it holds iff $x \cdot y = z$ (and has no solution when the product overflows). Hence $\mathrm{FO}[\le, \mathrm{BIT}] = \mathrm{FO}[\le, +, \times]$ on ordered structures, which is the class of $\mathrm{DLOGTIME}$-uniform $\mathrm{AC}^0$ queries.

## Proof sketch

Write the product as a sum of shifted copies of $x$ selected by the bits of $y$; compute column counts with the bit sum lemma and verify the carry chain in blocks of $O(\log\log n)$ bits packed into fixed tuples of words; parameters for the packing exist for all universe sizes beyond a constant, and small sizes are handled by a finite disjunction.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)

## Proof depends on

- [The bit sum lemma](bit-sum-lemma.md)
- [Addition is first-order definable from order and BIT](addition-definable-from-bit.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- D. A. M. Barrington, N. Immerman and H. Straubing, "On Uniformity within NC¹", Journal of Computer and System Sciences 41(3), 274–306, 1990.
