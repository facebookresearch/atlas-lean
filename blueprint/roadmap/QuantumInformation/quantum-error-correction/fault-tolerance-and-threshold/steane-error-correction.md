# Steane error correction

Let $Q$ be a CSS code built from classical codes with $C_2^{\perp} \subseteq C_1$ and $\dim C_1 - \dim C_2^{\perp} = 1$, so
that each block encodes one logical qubit as in Gottesman's Section 4.2, where $C_1$ corrects $t_1$ errors and
$C_2$ corrects $t_2$ errors, with $t \le \min(t_1, t_2)$, and suppose there are
[fault-tolerant preparation gadgets](fault-tolerant-preparation-gadget.md) for the encoded states $|\bar 0\rangle$ and
$|\bar +\rangle$. *Steane error correction* corrects bit flips by preparing an ancilla block in $|\bar +\rangle$, applying
transversal CNOT from the data block to it, measuring every ancilla qubit and decoding the outcome in $C_1$; it corrects
phase flips by preparing $|\bar 0\rangle$, applying transversal CNOT from the ancilla to the data, measuring every ancilla
qubit in the Hadamard basis and decoding in $C_2$; then it applies the deduced Pauli correction transversally. This
gadget is a [fault-tolerant EC gadget](fault-tolerant-error-correction-gadget.md): it satisfies EC A and EC B. The key
claim is that after the gadget the data block has errors only on qubits matching the positions of faults in the gadget;
an error pattern that the classical decoders misidentify differs from the true one by a codeword, which acts as a logical
operator and leaves a codeword. Transversal measurement of every qubit and classical decoding in the same way give a
fault-tolerant measurement gadget.

## Depends on

- [Distance of a CSS code](../css-codes/distance-of-a-css-code.md)
- [Fault-tolerant error-correction gadget](fault-tolerant-error-correction-gadget.md)
- [Fault-tolerant preparation gadget](fault-tolerant-preparation-gadget.md)
- [Fault-tolerant measurement gadget](fault-tolerant-measurement-gadget.md)

## Proof depends on

- [Transversal CNOT and CSS codes](../fault-tolerant-gates/transversal-cnot-and-css-codes.md)
- [Transversal gates are fault tolerant](../fault-tolerant-gates/transversal-gates-are-fault-tolerant.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.4 (Steane error correction, Figure 3, Claim 1 and its proof, and the fault-tolerant measurement of CSS codes by transversal measurement).
- A. M. Steane, *Active stabilization, quantum computation, and quantum state synthesis*, Phys. Rev. Lett. 78 (1997), 2252–2255, arXiv:quant-ph/9611027.
