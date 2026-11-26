# QMA with logarithmic-length witnesses equals BQP

If a promise problem has a QMA verifier with witness length $O(\log n)$, then it is in $\mathrm{BQP}$. Thus $\mathrm{QMA}_{\log} = \mathrm{BQP}$.

## Proof sketch

Amplify in place to error $2^{-r}$ with $r = m + 2$ where $m = O(\log n)$ is the witness length. Run the amplified verifier on the maximally mixed witness: its acceptance probability is the average over a basis of witnesses, at least $2^{-m}(1 - 2^{-r})$ for yes-instances and at most $2^{-r}$ for no-instances. The polynomial gap is then amplified by repetition inside BQP.

## Depends on

- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Proof depends on

- [Marriott-Watrous in-place amplification of QMA](in-place-qma-amplification.md)
- [BQP error reduction](../../bqp-error-reduction.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
