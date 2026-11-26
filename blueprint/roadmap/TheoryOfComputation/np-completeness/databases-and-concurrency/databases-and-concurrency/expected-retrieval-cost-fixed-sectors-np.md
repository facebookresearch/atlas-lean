# EXPECTED RETRIEVAL COST WITH m SECTORS is NP-complete

For every natural number $m \ge 2$, the decision problem EXPECTED RETRIEVAL COST WITH m SECTORS, with the number of sectors fixed to $m$ and a positive rational bound $K$, belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

This is not only the parent problem with $m$ fixed: the [parent](expected-retrieval-cost-np-complete.md) takes a positive integer bound. Since $d(i, i) = m - 1$, $d(i, j) + d(j, i) = m - 2$ for $i \ne j$ and $\sum_i p(R_i) = 1$, the cost equals $(m - 2)/2 + (m/2) \sum_i p(R_i)^2$; for $m = 2$, masses $p$ and $1 - p$ give cost $p^2 + (1 - p)^2 \le 1$, so every allocation meets every positive integer bound, while the bound $1/2$ asks for exact balance. With a rational bound the problem is, by the same identity, MINIMUM SUM OF SQUARES with $m$ parts: for sizes $s(a)$ with total $S$, take $p(a) = s(a)/S$ and $K = (m - 2)/2 + (m/2) J / S^2$. Garey and Johnson record MINIMUM SUM OF SQUARES as NP-complete for every fixed number of parts, which supports the rational variant.

## Sources

- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR4] EXPECTED RETRIEVAL COST, p. 227, comment: "NP-complete and solvable in pseudo-polynomial time for each fixed m ≥ 2".
- R. A. Cody and E. G. Coffman, Jr., "Record allocation for minimizing expected retrieval costs on drum-like storage devices", Journal of the ACM 23 (1976), 103-115, doi:10.1145/321921.321933.
- Garey and Johnson (1979), problem [SP19] MINIMUM SUM OF SQUARES, p. 225, comment: "NP-complete in the ordinary sense and solvable in pseudo-polynomial time for any fixed K".
