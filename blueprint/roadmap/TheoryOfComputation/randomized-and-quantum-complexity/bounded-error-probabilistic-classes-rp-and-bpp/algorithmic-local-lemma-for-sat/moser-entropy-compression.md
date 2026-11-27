# Entropy compression: Moser's algorithm runs in linear expected resamplings

Let $\varphi$ be an exact $k$-CNF formula with $m$ clauses on $n$ variables in which every clause shares a variable with at most $d$ other clauses, where $d+1\le 2^{k-3}$. Then on a tape of independent fair coin flips, Moser's algorithm performs at least $t$ resamplings with probability at most $2^{m+t(\log_2(d+1)+2-k)}\le 2^{m-t}$; in particular it terminates almost surely after $O(m)$ resamplings in expectation, and $\varphi$ is satisfiable.

## Proof sketch

Encode a run with $t$ resamplings by its final assignment ($n$ bits) and an execution log of at most $m + t(\log_2(d+1) + 2)$ bits that records the recursion tree (each step names which of the at most $d+1$ clauses sharing a variable with the current clause, the clause itself included, is fixed next); from these the $n + tk$ random bits consumed can be reconstructed. So at most $2^{n+m+t(\log_2(d+1)+2)}$ of the $2^{n+tk}$ prefixes of the tape lead to $t$ resamplings, and $\log_2(d+1)+2-k\le-1$.

## Depends on

- [Moser's resampling algorithm for $k$-SAT](moser-resampling-algorithm.md)

## Proof depends on

- [Fix preserves satisfied clauses](fix-preserves-satisfied-clauses.md)

## Sources

- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 2009.
- L. Fortnow, "A Kolmogorov Complexity Proof of the Lovász Local Lemma", Computational Complexity blog exposition, 2009.
