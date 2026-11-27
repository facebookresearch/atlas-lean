# Logarithmic-depth modular multiplication and inner products of words

For $w\ge1$, the product of two $w$-bit unsigned integers modulo $2^w$, and more generally the inner product modulo $2^w$ of two arrays of $k$ $w$-bit words, are computed by fan-in-two De Morgan circuits of size polynomial in $w$ and $k$ and depth $O(1+\log(wk))$ for $k\ge1$: all shifted partial products are formed in one layer, reduced along a balanced carry-save tree, and finished by a carry-lookahead addition. Modular subtraction is addition of the complement with an incoming carry. Hence these word operations are in $\mathsf{NC}^1$.

## Proof sketch

Each partial product is a masked shift of the first word by one bit of the second; a carry-save tree of $4$-to-$2$ reducers sums $wk$ words in logarithmic depth with $O(w^2k)$ gates, and a single logarithmic-depth adder resolves the final redundant pair.

## Depends on

- [The AC, TC and AC[q] hierarchies](ac-tc-and-acq-hierarchies.md)
- [Kogge–Stone carry-lookahead adder](../kogge-stone-adder/carry-lookahead-adder.md)

## Proof depends on

- [Carry-save addition and logarithmic-depth bit counting](carry-save-addition-and-bit-counting.md)

## Sources

- Ashok K. Chandra, Larry Stockmeyer, Uzi Vishkin, "Constant Depth Reducibility", SIAM Journal on Computing, 1984.
- Heribert Vollmer, "Introduction to Circuit Complexity: A Uniform Approach", Springer, 1999.
- Richard E. Ladner, Michael J. Fischer, "Parallel Prefix Computation", Journal of the ACM, 1980.
