# Moser–Tardos: constructive local lemma for $k$-SAT

Let $\varphi$ be an exact $k$-CNF formula with $m$ clauses and degree $d$ (each clause shares variables with at most $d$ others), and suppose $e(d+1) \le 2^k$. For any rule that repeatedly selects a violated clause and resamples its variables independently and uniformly, the expected number of times each clause is resampled is at most $1/d$, the expected total number of resamplings is at most $m/d$, and the process stops almost surely with a satisfying assignment. In the general (asymmetric) form, if weights $x_C \in (0,1)$ satisfy $2^{-k} \le x_C \prod_{D \sim C} (1 - x_D)$, the expected number of resamplings of $C$ is at most $x_C/(1-x_C)$.

## Proof sketch

Bound the expected number of witness trees of each size rooted at a clause: a witness tree appears with probability at most the product of $2^{-k}$ over its nodes, and the Galton–Watson branching process with the given weights dominates the count of trees.

## Depends on

- [Moser's resampling algorithm for $k$-SAT](moser-resampling-algorithm.md)
- [Lovász local lemma, general form](../../../Combinatorics/probabilistic-combinatorics/lovasz-local-lemma-general-finite.md)

## Proof depends on

- [Local lemma for $k$-SAT](local-lemma-for-k-sat.md)

## Sources

- R. A. Moser and G. Tardos, "A Constructive Proof of the General Lovász Local Lemma", Journal of the ACM 57(2), Article 11, 2010.
