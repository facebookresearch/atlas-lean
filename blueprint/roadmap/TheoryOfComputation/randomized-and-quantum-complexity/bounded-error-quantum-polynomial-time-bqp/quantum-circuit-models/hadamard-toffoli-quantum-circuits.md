# Quantum circuits over the Hadamard–Toffoli gate set

An $m$-qubit register has state space $\mathbb{C}^{\{0,1\}^m}$ with computational basis $|x\rangle$. A quantum circuit over the *Hadamard–Toffoli* gate set is a sequence of gates, each a Hadamard gate $H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$ on one qubit or a classical reversible gate (NOT, CNOT, Toffoli) on at most three qubits, all acting as the identity on the other qubits; the circuit's unitary is the product of the gate matrices, whose entries lie in $\{0,\pm1,\pm1/\sqrt2\}$. Bounded-error polynomial-time uniform families of circuits over this gate set decide exactly the languages in $\mathsf{BQP}$ (Shi; Aharonov). Measuring designated qubits in the computational basis at the end gives the output distribution.

## Depends on

- [Applying a quantum circuit to a state](../../../complexity-classes/time-and-space-complexity-classes/apply-circuit.md)
- [Encoded 2-local quantum gate](../../../complexity-classes/time-and-space-complexity-classes/qgate.md)
- [BQP](../../../complexity-classes/time-and-space-complexity-classes/bqp.md)

## Sources

- Yaoyun Shi, "Both Toffoli and Controlled-NOT Need Little Help to Universal Quantum Computing", Quantum Information and Computation 3(1), 84–92, 2003.
- Dorit Aharonov, "A Simple Proof that Toffoli and Hadamard are Quantum Universal", arXiv:quant-ph/0301040, 2003 (unrefereed; supplementary to Shi).
- A. Yu. Kitaev, A. H. Shen and M. N. Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, American Mathematical Society, 2002.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
