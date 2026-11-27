# Transversal gates are fault tolerant

Let a logical gate on $m$ blocks of an $[[n, 1, 2t + 1]]$ code be implemented by a
[transversal gate](transversal-gate.md) $U = \bigotimes_{i=1}^{n} U_i$, where $U_i$ acts on the $i$-th qubit of each of
the $m$ blocks. Then the gadget is a [fault-tolerant gate gadget](../fault-tolerance-and-threshold/fault-tolerant-gate-gadget.md):
it satisfies Gate A and Gate B. Conjugating an error on the $i$-th qubits through $U_i$ gives an error on the $i$-th qubits
only, so each incoming error or fault causes at most one error per block. All post-gate errors are supported on coordinate
indices carrying an input error or a gadget fault. Thus each output block has at most $s + \sum_j r_j$ affected qubits;
an error can spread to the same coordinate of another block (a transversal CNOT maps $X_i \otimes I$ to
$X_i \otimes X_i$), so a block's count can exceed its own incoming count $r_j$. Examples (see Related topics): logical Pauli operators chosen from the
normalizer are transversal in this sense for every stabilizer code, transversal Hadamard and phase-type gates implement
logical Clifford gates on Steane's code, and transversal CNOT implements the logical CNOT on every CSS code. Permuting the qubits of a block is not
allowed, since composing such gadgets could put two errors in one block.

## Depends on

- [Transversal gate](transversal-gate.md)
- [Fault-tolerant gate gadget](../fault-tolerance-and-threshold/fault-tolerant-gate-gadget.md)

## Related topics

- [Logical Pauli operators of a stabilizer code](../stabilizer-formalism/logical-pauli-operators-of-a-stabilizer-code.md): logical Pauli operators from the normalizer
- [Steane's seven-qubit code](../small-stabilizer-codes/steane-seven-qubit-code.md): transversal Clifford gates on Steane's code
- [Transversal CNOT and CSS codes](transversal-cnot-and-css-codes.md): transversal CNOT is the logical CNOT on CSS codes

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.3.
