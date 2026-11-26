# METRIC BOTTLENECK WANDERING SALESPERSON is NP-complete

The [decision problem](metric-bottleneck-wandering-salesperson-3.md) METRIC BOTTLENECK WANDERING SALESPERSON belongs to NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Hardness comes from a special case: with all distances equal to $1$ or $2$ (which always satisfy the triangle inequality) and $K = 1$, the question is whether the graph of the pairs at distance $1$ has a Hamiltonian path from $s$ to $f$, which is HAMILTONIAN PATH BETWEEN TWO POINTS.

## Sources

- P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000), entry MINIMUM METRIC BOTTLENECK WANDERING SALESPERSON PROBLEM.
- D. S. Hochbaum and D. B. Shmoys, "A unified approach to approximation algorithms for bottleneck problems", Journal of the ACM 33 (1986), 533-550, doi:10.1145/5925.5933 (approximable within 2, not within $2 - ε$ unless P = NP).
- M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH BETWEEN TWO POINTS (the special case with distances 1 and 2 described above); the tour version is [ND24] BOTTLENECK TRAVELING SALESMAN.
