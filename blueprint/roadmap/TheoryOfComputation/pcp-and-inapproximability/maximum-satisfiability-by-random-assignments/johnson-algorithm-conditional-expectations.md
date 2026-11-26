# Johnson's algorithm by conditional expectations

Given a CNF formula $\varphi$, Johnson's algorithm fixes the variables one at a time, each time choosing the value that does not increase the weight $W = \sum_{C} 2^{-|C|}$, where the sum is over clauses not yet satisfied and $|C|$ counts their unset distinct literals (a falsified clause has weight $1$). It runs in polynomial time and outputs an assignment falsifying at most $\sum_C 2^{-|C|}$ clauses, which is at most $m/2^k$ when every clause has at least $k$ distinct literals. In particular it is a $1 - 2^{-k}$ approximation for MAX-E$k$-SAT and a $1/2$ approximation for MAX-SAT.

## Proof sketch

$W$ equals the expected number of falsified clauses under a uniform completion; it is the average of its two values after fixing the next variable, so a greedy choice never increases it, and at the end $W$ counts falsified clauses exactly.

## Depends on

- [Unsatisfiability value of a CNF formula or CSP instance](unsatisfiability-value.md)

## Proof depends on

- [Random assignments satisfy $7/8$ of exact 3-CNF clauses](seven-eighths-random-assignment-bound.md)

## Sources

- D. S. Johnson, "Approximation Algorithms for Combinatorial Problems", Journal of Computer and System Sciences 9(3), 256–278, 1974.
- D. P. Williamson and D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011.
