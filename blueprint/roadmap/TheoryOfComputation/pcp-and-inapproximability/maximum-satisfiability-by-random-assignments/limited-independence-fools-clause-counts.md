# Limited independence fools clause counts

Let $\mathcal{D}$ be a $k$-wise independent distribution on assignments of $n$ variables with uniform marginals. Then for every CNF formula $\varphi$ the expected number of clauses falsified under $\mathcal{D}$ is at most $\sum_{C} 2^{-\min(k, |C|)}$, where $|C|$ is the number of distinct literals of a non-tautological clause. Since for fixed $k$ there are $k$-wise independent sample spaces of size $O(n^{\lceil k/2 \rceil})$, exhaustive search over such a space finds in polynomial time an assignment falsifying at most $m/2^k$ clauses of any formula all of whose clauses have at least $k$ distinct literals.

## Proof sketch

A clause with $j$ distinct literals is falsified exactly when $j$ specified variables take specified values; under $k$-wise independence this has probability $2^{-j}$ if $j \le k$ and at most $2^{-k}$ otherwise (restrict to $k$ of them). Polynomial-size sample spaces come from evaluating random low-degree polynomials over a finite field.

## Depends on

- [Unsatisfiability value of a CNF formula or CSP instance](unsatisfiability-value.md)

## Proof depends on

- [Random assignments satisfy $7/8$ of exact 3-CNF clauses](seven-eighths-random-assignment-bound.md)

## Sources

- N. Alon, L. Babai and A. Itai, "A Fast and Simple Randomized Parallel Algorithm for the Maximal Independent Set Problem", Journal of Algorithms 7(4), 567–583, 1986.
- N. Alon and J. H. Spencer, The Probabilistic Method, 4th ed., Wiley, 2016.
