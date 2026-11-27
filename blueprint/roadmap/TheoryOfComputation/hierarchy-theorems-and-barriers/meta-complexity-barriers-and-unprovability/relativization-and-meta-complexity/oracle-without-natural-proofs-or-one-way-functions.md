# A relativized world without natural proofs and without one-way functions

Ren and Santhanam give an oracle relative to which there are no $\mathsf{P/poly}$-natural properties useful against circuits of size $2^{\delta n}$, yet auxiliary-input one-way functions do not exist either. So basing one-way functions on the non-existence of natural proofs requires non-relativizing techniques.

There is a relativized world in which $\mathsf{P/poly}$-natural properties useful against $\mathsf{SIZE}[2^{\delta n}]$ do not exist and auxiliary-input one-way functions do not exist. In the same spirit, there are relativized worlds in which auxiliary-input one-way functions do not exist while GapMCSP, respectively GapMINKT, is hard on average under some samplable distribution with two-sided error.

## Expansion

The non-existence of natural proofs is equivalent to the zero-error average-case hardness of MCSP, and Santhanam showed with a relativizing proof that, under a universality conjecture about optimal hitting sets, it implies one-way functions; the oracle world shows that the universality conjecture fails relative to an oracle. Because one-way functions are equivalent to two-sided-error average-case hardness of MINKT under the uniform distribution, and because the absence of auxiliary-input one-way functions forces $\mathsf{CZK} = \mathsf{BPP}$, the same world shows that extending Hirahara's worst-case to average-case reduction to two-sided error over the uniform distribution, or proving $\mathrm{GapMINKT} \in \mathsf{CZK}$, needs non-relativizing techniques.

## Depends on

- [Natural property](../../natural-proofs-barrier/natural-property.md)
- [Auxiliary-input one-way functions](../../../pseudorandomness-and-one-way-functions/worst-case-characterizations-of-one-way-functions/auxiliary-input-one-way-functions.md)
- [The time-bounded Kolmogorov complexity problem MINKT](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/the-minkt-problem.md)

## Proof depends on

None.

## Sources

- Hanlin Ren and Rahul Santhanam, "A Relativization Perspective on Meta-Complexity", *STACS* 2022, LIPIcs 219, Article 54, DOI 10.4230/LIPIcs.STACS.2022.54 (abstract item 4 and Theorems 16, 17 and 18, Section 2.3; proof overview in Section 3.3).
