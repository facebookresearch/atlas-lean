# Marriott-Watrous: QIP equals QMAM

$\mathrm{QIP}(3) = \mathrm{QMAM}$, and hence $\mathrm{QIP} = \mathrm{QMAM}$. Moreover, for every polynomial $r$, every problem in $\mathrm{QIP}$ has a QMAM protocol with completeness $1$ and soundness $1/2 + 2^{-r(n)}$, and parallel repetition reduces the soundness to $2^{-r(n)}$.

## Proof sketch

Given a three-message protocol with perfect completeness, Arthur flips a coin deciding whether to run the verifier's final step forward on Merlin's second message or to check, by inverting the first step, that Merlin's first message was produced honestly. A prover passing both tests with high probability yields a prover for the original protocol; the converse simulation is direct.

## Depends on

- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)
- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)

## Proof depends on

- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
