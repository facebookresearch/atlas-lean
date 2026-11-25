# Wasserstein distance between barcodes

Let $B,C$ be finite multisets of graded bars. For a degree-preserving partial matching $M$ of their occurrences, let $A_M$ be the multiset consisting of the maximum endpoint discrepancy of each matched pair and the distance to the diagonal of every unmatched bar in either barcode. Two infinite deaths contribute zero death discrepancy; a finite and an infinite death have infinite distance. The distance to the diagonal is half the bar's length, infinite for a bar with infinite death. For $p\ge1$ the $p$-Wasserstein distance is

$$W_p(B,C)=\inf_M\left(\sum_{a\in A_M}a^p\right)^{1/p}.$$

The sum counts multiplicities; the empty sum is zero. The same expression is defined for every real $p$ using extended nonnegative real powers and the convention $1/0=0$, without a metric assertion outside the usual range.

## Sources

- [Topological Data Analysis, Chapter 6](https://ti.inf.ethz.ch/ew/courses/TDA24/Chapter6.pdf).
