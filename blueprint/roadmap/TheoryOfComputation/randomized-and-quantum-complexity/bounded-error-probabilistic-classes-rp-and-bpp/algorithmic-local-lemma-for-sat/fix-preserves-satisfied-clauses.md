# Fix preserves satisfied clauses

In Moser's algorithm, if $\mathrm{Fix}(C)$ returns, then $C$ is satisfied on return and every clause that was satisfied when $\mathrm{Fix}(C)$ was called is still satisfied. Consequently the top-level loop calls $\mathrm{Fix}$ at most once per clause, and if the algorithm terminates it outputs a satisfying assignment.

## Proof sketch

Resampling the variables of $C$ can only falsify neighbours of $C$; the inner loop repairs all violated neighbours before returning, and by induction each recursive call preserves previously satisfied clauses.

## Depends on

- [Moser's resampling algorithm for $k$-SAT](moser-resampling-algorithm.md)

## Sources

- R. A. Moser, "A Constructive Proof of the Lovász Local Lemma", Proceedings of the 41st ACM Symposium on Theory of Computing (STOC), 343–350, 2009, Algorithm 2.1 and its analysis.
- L. Fortnow, "A Kolmogorov Complexity Proof of the Lovász Local Lemma", Computational Complexity blog, 2009 (unrefereed write-up of Moser's STOC 2009 talk; source of the entropy-compression encoding and of the constant $2^{k-3}$).
