# Transversal gates are fault tolerant

Let a logical gate on $m$ blocks of an $[[n, 1, 2t + 1]]$ code be implemented by a
[transversal gate](transversal-gate.md) $U = \bigotimes_{i=1}^{n} U_i$, where $U_i$ acts on the $i$-th qubit of each of
the $m$ blocks. Then the gadget is a [fault-tolerant gate gadget](../fault-tolerance-and-threshold/fault-tolerant-gate-gadget.md):
it satisfies Gate A and Gate B. Conjugating an error on the $i$-th qubits through $U_i$ gives an error on the $i$-th qubits
only, so each incoming error or fault causes at most one error per block; errors can be moved after the gate without
increasing the number of affected qubits in any block. Logical Pauli operators chosen from the normalizer are transversal
in this sense for every stabilizer code, transversal Hadamard and phase-type gates implement logical Clifford gates on
Steane's code, and transversal CNOT implements the logical CNOT on every CSS code. Permuting the qubits of a block is not
allowed, since composing such gadgets could put two errors in one block.

## Depends on

- [Transversal gate](transversal-gate.md)
- [Fault-tolerant gate gadget](../fault-tolerance-and-threshold/fault-tolerant-gate-gadget.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.3.
