# Entropy compression: Moser's algorithm runs in linear expected resamplings

Let $\varphi$ be an exact $k$-CNF formula with $m$ clauses on $n$ variables in which every clause shares a variable with fewer than $2^{k-3}$ other clauses. Then on a tape of independent fair coin flips, Moser's algorithm performs at least $t$ resamplings with probability at most $2^{-(t - m - n)}$-type exponentially small in $t$; in particular it terminates almost surely after $O(m)$ resamplings in expectation, and $\varphi$ is satisfiable.

## Proof sketch

Encode a run with $t$ resamplings by its final assignment ($n$ bits) and an execution log of at most $m + t(\log_2 d + O(1))$ bits that records the recursion tree; from these the $n + tk$ random bits consumed can be reconstructed. Since $\log_2 d + O(1) < k$ under the degree hypothesis, the log is shorter than the bits it determines, so by counting only an exponentially small fraction of tapes can run that long.

## Depends on

- [Moser's resampling algorithm for $k$-SAT](moser-resampling-algorithm.md)

## Proof depends on

- [Fix preserves satisfied clauses](fix-preserves-satisfied-clauses.md)

## Sources

- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 2009.
- L. Fortnow, "A Kolmogorov Complexity Proof of the Lovász Local Lemma", Computational Complexity blog exposition, 2009.
