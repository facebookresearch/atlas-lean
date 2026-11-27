# Quantum interaction semantics

An $m$-message quantum interaction between a verifier and a prover uses a message register and private registers of fixed
finite dimensions. The parties alternate: each applies a channel (completely positive trace-preserving map) to its
private register and the message register. The verifier always receives the last message, so it sends the first message
exactly when $m$ is even. After receiving the last message the verifier applies a binary measurement with an accepting
outcome. For a fixed verifier, the value of the
interaction is the supremum, over all prover channels of the given dimensions (and over all finite prover private
dimensions), of the probability of acceptance. A classical-message protocol embeds by having the verifier apply the
completely dephasing channel to the message register before and after each use, so that the prover's messages are
effectively computational-basis states.

## Depends on

- [Positive-operator-valued measurements and the Born rule](../../QuantumInformation/quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)
- [Quantum channel](../../QuantumInformation/quantum-operations/quantum-channel.md)

## Sources

- J. Watrous, "Quantum computational complexity", arXiv:0804.3401, Section VI.1 (verifier circuits, private memory and message qubits, the verifier receives the last message, prover operations arbitrary, acceptance by measuring an output qubit). <https://arxiv.org/abs/0804.3401>
- S. Aaronson, MIT 6.845 Quantum Complexity Theory, Lecture 17 (scribe notes), §2 (quantum interactive proofs: Arthur and Merlin exchange quantum messages). <https://old.ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-845-quantum-complexity-theory-fall-2010/lecture-notes/MIT6_845F10_lec17.pdf>
