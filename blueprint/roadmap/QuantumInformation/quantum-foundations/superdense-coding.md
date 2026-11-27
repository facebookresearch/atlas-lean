# Superdense coding

Let Alice and Bob share the two-qubit state $(\lvert 00 \rangle + \lvert 11 \rangle)/\sqrt 2$, Alice holding the first qubit. For two
classical bits $(b_1, b_2)$, Alice applies $Z^{b_1} X^{b_2}$ to her qubit and sends it to Bob over a noiseless quantum
channel. The four resulting states are, up to global phases, the four Bell states, which form an orthonormal basis, so
Bob's projective measurement in the Bell basis recovers $(b_1, b_2)$ with probability $1$.

## Depends on

- [Bell basis and maximally entangled states](bell-basis-and-maximally-entangled-states.md)
- [Positive-operator-valued measurements and the Born rule](../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Chapter 1, Exercise 14 (Alice applies $X$ if $a = 1$, then $Z$ if $b = 1$, and sends her qubit; Bob recovers $a$ and $b$) and the hint to Exercise 15(b) ("This exercise is just superdense coding in disguise"). <https://arxiv.org/pdf/1907.09415v6>
