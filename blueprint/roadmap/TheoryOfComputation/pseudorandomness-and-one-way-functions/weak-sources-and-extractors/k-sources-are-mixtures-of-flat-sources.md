# Every k-source is a mixture of flat k-sources

Let $\Omega$ be finite and $K \ge 1$ an integer. A distribution on $\Omega$ all of whose outcomes have probability at most $1/K$ is a convex combination of uniform distributions on subsets of exactly $K$ outcomes. In particular, for an integer $k \ge 0$ the $k$-sources on $\Omega$ are exactly the mixtures of flat sources on sets of size $2^k$.

## Proof sketch

Scale the masses by $K$ to get a point of $[0,1]^\Omega$ with coordinate sum $K$. If two coordinates lie strictly between $0$ and $1$, moving weight between them writes the point as a convex combination of two points with fewer fractional coordinates; when none remain the point is the indicator of a $K$-set. Induct on the number of fractional coordinates.

## Depends on

- [k-sources, (k, ε)-sources and flat sources](weak-random-sources.md)

## Sources

- B. Chor and O. Goldreich, "Unbiased Bits from Sources of Weak Randomness and Probabilistic Communication Complexity", SIAM Journal on Computing 17(2), 230–261, 1988.
- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1–3), 1–336, 2012, Lemma 6.10.
