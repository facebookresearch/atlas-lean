# The bit sum lemma

There is a first-order formula $\mathrm{BSUM}(x, y)$ over $\{\le, \mathrm{BIT}\}$ such that on every canonically ordered universe, $\mathrm{BSUM}(x,y)$ holds iff $y$ is the number of $1$ bits in the binary expansion of $x$; such a $y$ always exists and is unique. More generally first-order logic with $\mathrm{BIT}$ can count up to polylogarithmic quantities by packing small numbers into the bits of single elements.

## Proof sketch

Pack partial sums of a balanced binary tree over the $O(\log n)$ bit positions into the bits of a constant number of elements, each node value using $O(\log\log n)$ bits, and verify all node equations locally with PLUS on these short fields.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)

## Proof depends on

- [Addition is first-order definable from order and BIT](addition-definable-from-bit.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- D. A. M. Barrington, N. Immerman and H. Straubing, "On Uniformity within NC¹", Journal of Computer and System Sciences 41(3), 274–306, 1990.
