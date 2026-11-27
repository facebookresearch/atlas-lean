# Local contraction preserves even delta-matroids

Let $R$ be an even delta-matroid of arity $n$ and $r \in R$ a feasible reference tuple. For a set $P$ of internal positions, the *contraction* keeps the tuples of $R$ that differ from $r$ in at most one internal position, and projects away the internal positions while recording (as a new connector coordinate) whether a change occurred. The contracted relation is again an even delta-matroid, and its rows are witnessed by actual rows of $R$ with zero or exactly one deviation.

## Proof sketch

The contracted relation is the composition (gadget construction) of $R$ with the relation $Z$ on the internal positions and the connector whose tuples are $r$ restricted to $P$ with connector $0$, and the tuples obtained from it by flipping one internal position together with the connector. $Z$ is an even delta-matroid, and compositions of (even) delta-matroids are (even) delta-matroids (Bouchet–Cunningham), which is how Kazda, Kolmogorov and Rolínek show that a contracted blossom constraint is again an even delta-matroid.

## Depends on

- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Sources

- A. Bouchet and W. H. Cunningham, "Delta-Matroids, Jump Systems, and Bisubmodular Polyhedra", SIAM Journal on Discrete Mathematics 8(1), 17–32, 1995.

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Section 5.3 and Proposition 6.
