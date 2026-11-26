# Marriott-Watrous: QIP equals QMAM

$\mathrm{QIP}(3) = \mathrm{QMAM}$, and hence $\mathrm{QIP} = \mathrm{QMAM}$. Moreover the QMAM protocol can be taken with completeness $1$ and soundness $1/2 + \varepsilon$, amplifiable by parallel repetition.

## Proof sketch

Given a three-message protocol with perfect completeness, Arthur flips a coin deciding whether to run the verifier's final step forward on Merlin's second message or to check, by inverting the first step, that Merlin's first message was produced honestly. A prover passing both tests with high probability yields a prover for the original protocol; the converse simulation is direct.

## Depends on

- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)
- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)

## Proof depends on

- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)
- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
