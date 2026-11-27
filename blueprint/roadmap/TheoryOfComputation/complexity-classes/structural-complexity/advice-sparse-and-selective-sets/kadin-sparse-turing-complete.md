# Kadin: a sparse Turing-complete set for NP collapses PH to P^{NP[log]}

If there is a sparse $S\in\mathsf{NP}$ such that $\mathrm{SAT}\le^{p}_{T}S$, then

$$
\mathsf{PH}=\mathsf{P}^{\mathsf{NP}[O(\log n)]},
$$

the class of languages decided in polynomial time with $O(\log n)$ adaptive queries to an $\mathsf{NP}$ oracle.

## Proof sketch

With $O(\log n)$ NP queries, binary search computes the exact census of $S$ up to the relevant length. Given the census, an NP machine can guess all members of $S$ of that length and verify them, so it can answer queries to $S$ both positively and negatively; this places $\Sigma_2^p$, hence $\mathsf{PH}$, in $\mathsf{P}^{\mathsf{NP}[O(\log n)]}$.

## Depends on

- [Sparse decision problems](../../mahaney-s-theorem/sparse.md)
- [The polynomial hierarchy](../../time-and-space-complexity-classes/ph.md)
- [Bounded-query oracle classes and P^{NP[O(log n)]}](bounded-query-classes.md)

## Sources

- Jim Kadin, "P^NP[O(log n)] and Sparse Turing-Complete Sets for NP", Journal of Computer and System Sciences 39(3), 1989.
