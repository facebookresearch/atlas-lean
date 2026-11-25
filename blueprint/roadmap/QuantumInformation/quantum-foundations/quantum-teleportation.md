# Quantum teleportation

Suppose Alice holds a qubit in an arbitrary state $\alpha|0\rangle + \beta|1\rangle$ and shares the state
$\frac{1}{\sqrt2}(|00\rangle + |11\rangle)$ with Bob. Alice applies a CNOT from her input qubit to her half of the
shared pair, then a Hadamard gate to the input qubit, and measures both qubits in the computational basis,
obtaining bits $(a, b)$. Each outcome occurs with probability $1/4$, independently of the input state, and after
Bob applies $X^b$ and then $Z^a$ to his qubit, its state is $\alpha|0\rangle + \beta|1\rangle$. The protocol uses
one shared entangled pair and two bits of classical communication.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Measurements (POVM, projective) and the Born rule.

## Depends on

- [Bell basis and maximally entangled states](bell-basis-and-maximally-entangled-states.md)
- [Unitary evolution and elementary gates](unitary-evolution-and-elementary-gates.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §1.5. <https://arxiv.org/pdf/1907.09415v6>
