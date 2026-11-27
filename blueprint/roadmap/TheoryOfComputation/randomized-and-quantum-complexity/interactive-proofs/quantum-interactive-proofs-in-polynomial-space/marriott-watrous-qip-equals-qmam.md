# Marriott-Watrous: QIP equals QMAM

$\mathrm{QIP}(3) = \mathrm{QMAM}$, and hence $\mathrm{QIP} = \mathrm{QMAM}$. Specifically, for every polynomial $r$, every problem in $\mathrm{QIP}$ admits a **single-coin** QMAM protocol (where Arthur's public message is a single uniformly random bit) with completeness $1$ and soundness at most $1/2 + 2^{-r(n)}$ (Marriott–Watrous, Theorem 5.4), and parallel repetition yields a multi-coin QMAM protocol with completeness $1$ and soundness at most $2^{-r(n)}$, giving $\mathrm{QIP} = \mathrm{QMAM}(1, 2^{-r(n)})$ (Corollary 5.6).

## Proof sketch

Given a three-message protocol with perfect completeness, Arthur flips a coin deciding whether to run the verifier's final step forward on Merlin's second message or to check, by inverting the first step, that Merlin's first message was produced honestly. A prover passing both tests with high probability yields a prover for the original protocol; the converse simulation is direct.

## Depends on

- [Quantum Merlin-Arthur-Merlin games (QMAM)](quantum-merlin-arthur-merlin-games.md)
- [Message-bounded quantum interactive proof classes QIP(m)](message-bounded-quantum-interactive-proof-classes.md)

## Proof depends on

- [Kitaev-Watrous: quantum interactive proofs parallelize to three messages](kitaev-watrous-three-message-parallelization.md)

## Sources

- Chris Marriott, John Watrous, "Quantum Arthur-Merlin games", Computational Complexity 14 (2005); arXiv:cs/0506068.
