# Effective proof length of non-adaptive PCP verifiers, and PCP(log, poly) ⊆ NP

A non-adaptive PCP verifier using $r(n)$ random bits and $q(n)$ queries reads, over all its random strings, at most $2^{r(n)}q(n)$ distinct proof positions. Consequently, for PCP systems with perfect completeness (on yes-instances some proof is always accepted) and soundness error $1/2$ (on no-instances every proof is rejected with probability at least $1/2$), every language with such a system of randomness complexity $O(\log n)$ and polynomial query complexity is in $\mathsf{NP}$: the restriction of the proof to the polynomially many relevant positions is an NP certificate, verified by running the verifier on all $2^{O(\log n)}$ random strings.

## Proof sketch

For each random string the query set is determined, so the union over random strings has at most $2^{r}q$ elements; an NP machine guesses the bits at those positions and accepts iff the verifier accepts on every random string.

Derived (the cited sources state the inclusion for perfect completeness and soundness $1/2$): the same holds for the two-sided class $\mathrm{PCP}(O(\log n),\mathrm{poly}(n))$ of the linked definition (acceptance probability at least $2/3$ versus at most $1/3$), since the NP machine can compute the exact acceptance fraction over all $2^{O(\log n)}$ random strings and accept iff it is at least $2/3$.

## Depends on

- [Probabilistically checkable proofs](../../complexity-classes/time-and-space-complexity-classes/pcp.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Definition 9.14, Section 9.3.1 ("a bound of $2^r \cdot q$ holds for non-adaptive systems") and Proposition 9.15 ("In particular, $\mathcal{PCP}(\log, \mathrm{poly}) \subseteq \mathcal{NP}$"); numbering of the 2007 public draft on the author's homepage.
- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009, Chapter 11.
