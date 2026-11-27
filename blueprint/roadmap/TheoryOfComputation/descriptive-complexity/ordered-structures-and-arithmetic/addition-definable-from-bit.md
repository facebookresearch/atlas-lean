# Addition is first-order definable from order and BIT

There is a first-order formula $\mathrm{PLUS}(x, y, z)$ over $\{\le, \mathrm{BIT}\}$ such that on every canonically ordered universe $\{0,\dots,n-1\}$, $n \ge 2$, it holds exactly when $x + y = z$ (with no solution when $x + y \ge n$). Consequently comparison with fixed numerals, multiplication by fixed numerals, quotient and remainder by fixed divisors, exact binary shifts and the predicates "is a power of two" and "highest set bit" are first-order definable.

## Proof sketch

Define the carry into bit position $i$ by the generate/propagate formula: some position $j < i$ has $\mathrm{BIT}(x,j) \wedge \mathrm{BIT}(y,j)$ and every position strictly between has at least one of the bits set; then $z$'s bit $i$ is the XOR of the bits of $x$, $y$ and the carry, quantifying over positions $i < \log_2 n$ represented by elements.

## Depends on

- [Canonically ordered structures with BIT](canonically-ordered-structures-with-bit.md)

## Sources

- N. Immerman, Descriptive Complexity, Springer, 1999.
- D. A. M. Barrington, N. Immerman and H. Straubing, "On Uniformity within NC¹", Journal of Computer and System Sciences 41(3), 274–306, 1990.
