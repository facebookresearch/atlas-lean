# QMA is contained in PP via in-place amplification

$\mathrm{QMA} \subseteq \mathrm{PP}$: every promise problem with a polynomial-time quantum verifier for polynomial-size quantum witnesses (bounded error) is decided by a probabilistic polynomial-time machine with unbounded error.

## Proof sketch

After in-place amplification to error $2^{-(m+2)}$, the acceptance probability of the verifier on the maximally mixed witness is at least $2^{-m}(1 - 2^{-m-2})$ on yes-instances and at most $2^{-m-2}$ on no-instances. This acceptance probability is a ratio of a GapP function to a power of two, as in the proof that BQP is contained in PP, so comparing it with the threshold $2^{-m-1}$ is a PP computation.

## Depends on

- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)
- [Probabilistic polynomial time with unbounded error](../../../complexity-classes/time-and-space-complexity-classes/pp.md)

## Proof depends on

- [Marriott-Watrous in-place amplification of QMA](in-place-qma-amplification.md)
- [BQP is contained in PP](../bqp-subset-pp.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
