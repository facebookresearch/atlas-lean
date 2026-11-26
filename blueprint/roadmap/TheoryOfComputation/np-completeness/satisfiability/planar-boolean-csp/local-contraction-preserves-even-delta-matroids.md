# Local contraction preserves even delta-matroids

Let $R$ be an even delta-matroid of arity $n$ and $r \in R$ a feasible reference tuple. For a set $P$ of internal positions, the *contraction* keeps the tuples of $R$ that differ from $r$ in at most one internal position, and projects away the internal positions while recording (as a new connector coordinate) whether a change occurred. The contracted relation is again an even delta-matroid, and its rows are witnessed by actual rows of $R$ with zero or exactly one deviation.

## Proof sketch

The delta-matroid exchange axiom applied to two retained rows yields an exchange partner that changes at most one internal position, and parity is preserved by the connector bookkeeping.

## Depends on

- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
