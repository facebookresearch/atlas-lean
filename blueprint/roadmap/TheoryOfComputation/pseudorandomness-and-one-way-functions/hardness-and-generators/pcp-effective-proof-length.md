# Effective proof length of non-adaptive PCP verifiers, and PCP(log, poly) ⊆ NP

A non-adaptive PCP verifier using $r(n)$ random bits and $q(n)$ queries reads, over all its random strings, at most $2^{r(n)}q(n)$ distinct proof positions. Consequently every language in $\mathsf{PCP}(O(\log n),\mathrm{poly}(n))$ is in $\mathsf{NP}$: the restriction of the proof to the polynomially many relevant positions is an NP certificate, verified by running the verifier on all $2^{O(\log n)}$ random strings.

## Proof sketch

For each random string the query set is determined, so the union over random strings has at most $2^{r}q$ elements; an NP machine guesses the bits at those positions and accepts iff every random string accepts (perfect completeness) or the acceptance fraction exceeds the threshold.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 9.15 (numbering of the 2007 public draft).
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 11.
