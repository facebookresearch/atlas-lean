# Kolmogorov-complexity form of Moser's argument

For an exact $k$-CNF formula $\varphi$ on $n$ variables with $m$ clauses and degree $d < 2^{k-3}$, there is an explicit decoding method that reconstructs the first $n + tk$ bits of any random tape on which Moser's algorithm performs $t$ resamplings from a description of length at most $n + m + t(k - 1)$-bits. Hence a tape of Kolmogorov complexity at least its length (an incompressible string) causes the algorithm to stop after $O(m + n)$ resamplings, which proves that $\varphi$ is satisfiable.

## Proof sketch

The description is the final assignment followed by the execution log; decoding replays the recursion backwards, recovering each resampled block from the clause that was violated before it was resampled. Incompressible strings exist of every length.

## Depends on

- [Moser's resampling algorithm for $k$-SAT](moser-resampling-algorithm.md)
- [Incompressible strings exist at every length](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/exists-incompressible.md)

## Proof depends on

- [Entropy compression: Moser's algorithm runs in linear expected resamplings](moser-entropy-compression.md)
- [Incompressible strings exist at every length](../../kolmogorov-complexity/incompressible-strings-and-kolmogorov-complexity/exists-incompressible.md)

## Sources

- L. Fortnow, "A Kolmogorov Complexity Proof of the Lovász Local Lemma", Computational Complexity blog exposition, 2009.
- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 2009.
