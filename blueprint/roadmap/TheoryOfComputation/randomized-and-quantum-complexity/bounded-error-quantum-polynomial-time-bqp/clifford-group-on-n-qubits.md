# The Clifford group on $n$ qubits

The $n$-qubit Clifford group is the group of unitaries $U$ on $(\mathbb{C}^2)^{\otimes n}$ that map the
[Pauli group](pauli-group-on-n-qubits.md) to itself under conjugation,

$$\mathcal{C}_n = \{\, U : U \mathcal{P}_n U^* = \mathcal{P}_n \,\}.$$

It contains every scalar unitary $e^{i\theta} I$ and the Pauli group itself. The *projective Clifford group* is the
quotient $\mathcal{C}_n / U(1)$ by the scalars, since $U$ and $e^{i\theta} U$ act identically by conjugation; finite
descriptions such as tableaux and generation by gates refer to it. Circuits of the Hadamard gate $H$, the phase gate
$S = \operatorname{diag}(1, i)$ and CNOT, on any qubits and tensored with the identity elsewhere, are called Clifford
circuits; that these gates lie in $\mathcal{C}_n$ is a separate result (see Related topics).

## Depends on

- [The Pauli group on $n$ qubits](pauli-group-on-n-qubits.md)

## Related topics

- [Conjugation of Pauli operators by $H$, $S$ and CNOT](../../../QuantumInformation/quantum-error-correction/clifford-group/conjugation-of-pauli-operators-by-h-s-and-cnot.md): $H$, $S$ and CNOT lie in the Clifford group.

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.3 (the normalizer of the Pauli group).
- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 3.5 ("the Clifford group ... the set of unitary operators $U$ such that $U Q U^\dagger$ is a Pauli operator for all Pauli $Q$").
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 20.2.
