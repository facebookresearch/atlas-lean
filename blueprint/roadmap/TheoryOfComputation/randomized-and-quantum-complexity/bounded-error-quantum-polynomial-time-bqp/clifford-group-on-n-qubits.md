# The Clifford group on $n$ qubits

The $n$-qubit Clifford group is the group of unitaries $U$ on $(\mathbb{C}^2)^{\otimes n}$ that map the
[Pauli group](pauli-group-on-n-qubits.md) to itself under conjugation,

$$\mathcal{C}_n = \{\, U : U \mathcal{P}_n U^* = \mathcal{P}_n \,\}.$$

It contains every scalar unitary $e^{i\theta} I$ and the Pauli group itself, and it is often taken modulo the scalars,
since $U$ and $e^{i\theta} U$ act identically by conjugation. The Hadamard gate $H$, the phase gate
$S = \operatorname{diag}(1, i)$ and CNOT, on any qubits and tensored with the identity elsewhere, lie in $\mathcal{C}_n$
by the [conjugation rules](../../../QuantumInformation/quantum-error-correction/clifford-group/conjugation-of-pauli-operators-by-h-s-and-cnot.md);
circuits of these gates are Clifford circuits.

## Depends on

- [The Pauli group on $n$ qubits](pauli-group-on-n-qubits.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.3 (the normalizer of the Pauli group).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.5 ("the Clifford group ... the set of unitary operators $U$ such that $U Q U^\dagger$ is a Pauli operator for all Pauli $Q$").
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 20.2.
