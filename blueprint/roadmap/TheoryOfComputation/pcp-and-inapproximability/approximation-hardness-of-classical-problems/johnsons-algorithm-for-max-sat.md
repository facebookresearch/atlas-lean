# Johnson's algorithm approximates MAX-SAT within 1 − 2^{−k}

Johnson's algorithm (the method of conditional expectations applied to a uniformly random assignment) runs in polynomial time and, on every CNF formula all of whose clauses contain at least $k$ distinct literals, outputs an assignment satisfying at least a $1 - 2^{-k}$ fraction of the clauses, hence at least $1 - 2^{-k}$ times the optimum. In particular it is a $7/8$-approximation algorithm for MAX-E3SAT.

## Proof sketch

A uniformly random assignment satisfies a clause with $k$ distinct literals with probability $1 - 2^{-k}$. Fixing the variables one by one, always choosing the value that does not decrease the conditional expectation of the number of satisfied clauses, ends at an assignment at least as good as the expectation.

## Depends on

- [The MAX-3SAT objective](../approximability-of-max-3sat/max3-satval.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)

## Sources

- D. S. Johnson, "Approximation Algorithms for Combinatorial Problems", Journal of Computer and System Sciences 9(3), 1974.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
