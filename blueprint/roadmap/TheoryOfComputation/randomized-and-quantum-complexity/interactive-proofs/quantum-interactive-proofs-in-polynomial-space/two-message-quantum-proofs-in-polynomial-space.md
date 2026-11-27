# Jain-Upadhyay-Watrous: QIP(2) is contained in PSPACE

$\mathrm{QIP}(2) \subseteq \mathrm{PSPACE}$: every problem having a two-message (verifier then prover) quantum interactive proof with bounded error is decidable in polynomial space.

## Proof sketch

The optimal acceptance probability of a two-message protocol is the value of a min-max semidefinite program over density operators of exponential dimension. A matrix multiplicative weights iteration with a constant accuracy target converges in $\mathrm{poly}(n)$ rounds, each computable in $\mathrm{NC}(\mathrm{poly})$ by the matrix exponential lemma; Borodin's theorem converts the polynomial-depth computation into polynomial space.

## Depends on

- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)
- [Polynomial space for decision problems](../../../complexity-classes/time-and-space-complexity-classes/pspace.md)

## Proof depends on

- [Regret bound for the matrix multiplicative weights update](matrix-multiplicative-weights-regret-bound.md)
- [Matrix exponentials of exponential-dimension matrices in polynomial depth](matrix-exponentials-in-polynomial-depth.md)
- [Borodin: NC(poly) = PSPACE](borodin-polynomial-depth-equals-polynomial-space.md)

## Sources

- Rahul Jain, Sarvagya Upadhyay, John Watrous, "Two-message quantum interactive proofs are in PSPACE", FOCS (2009); arXiv:0905.1300.
