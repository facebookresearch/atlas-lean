# One-way functions put NP outside BPP

If a one-way function exists, then $\mathsf{NP} \not\subseteq \mathsf{BPP}$.

## Proof sketch

Consider the NP language of pairs $(y, w)$ such that some preimage of $y$ extends the prefix $w$. A bounded-error polynomial-time decider for it, amplified to error $2^{-2n}$, recovers a preimage bit by bit by self-reducibility, inverting $f$ with probability close to one on every image.

## Depends on

- [One-way function families](../../complexity-classes/time-and-space-complexity-classes/is-one-way-function.md)
- [The complexity class NP](../../complexity-classes/the-classes-p-np-and-conp/np.md)
- [BPP](../../complexity-classes/time-and-space-complexity-classes/bpp.md)

## Proof depends on

- [Error reduction for BPP](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/error-reduction-for-bpp.md)
- [One-way functions imply P ≠ NP](../owf-implies-p-ne-np.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- S. Arora and B. Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009.
