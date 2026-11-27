# Random assignments satisfy $7/8$ of exact 3-CNF clauses

If every clause of a CNF formula $\varphi$ has exactly three literals on distinct variables, then a uniformly random assignment falsifies each clause with probability $1/8$, so the expected number of falsified clauses is $m/8$ and some assignment falsifies at most $\lfloor m/8 \rfloor$ clauses; hence $\mathrm{uval}(\varphi) \le 1/8$. More generally, if every clause has at least $k$ distinct literals and no complementary pair, some assignment falsifies at most $m/2^k$ clauses.

## Proof sketch

Linearity of expectation over clauses, and existence of an assignment at most the mean.

## Depends on

- [Unsatisfiability value of a CNF formula or CSP instance](unsatisfiability-value.md)

## Proof depends on

- [Johnson's random assignment](../../../ComputerScience/approximation-algorithms/randomized-rounding-for-max-sat/clause-sat-prob-half.md)

## Sources

- D. S. Johnson, "Approximation Algorithms for Combinatorial Problems", Journal of Computer and System Sciences 9(3), 256–278, 1974.
- J. Håstad, "Some Optimal Inapproximability Results", Journal of the ACM 48(4), 798–859, 2001.
