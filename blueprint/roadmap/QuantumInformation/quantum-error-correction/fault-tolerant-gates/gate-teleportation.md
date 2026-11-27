# Gate teleportation

Let $U$ be a one-qubit unitary and $|\Phi_U\rangle = (I \otimes U)(|00\rangle + |11\rangle)/\sqrt{2}$. Perform a Bell
measurement on a qubit in state $|\psi\rangle$ and the first qubit of $|\Phi_U\rangle$, as in
[teleportation](../../quantum-foundations/quantum-teleportation.md); the outcome determines a Pauli operator
$Q \in \{I, X, Y, Z\}$. Then the second qubit of $|\Phi_U\rangle$ is left in the state $U Q |\psi\rangle$ up to a global
phase, and applying $U Q U^{*}$ to it gives $U |\psi\rangle$. If $U$ lies in level $k \ge 2$ of the
[Clifford hierarchy](../clifford-group/clifford-hierarchy.md), then $U Q U^{*}$ lies in level $k - 1$; in particular, for a
Clifford $U$ the correction is a Pauli operator, and for $U$ in the third level (such as $T$) it is a Clifford operator.
So a gate of level $k \ge 2$ is implemented by gates of level $k - 1$, Bell measurements and the prepared resource state
$|\Phi_U\rangle$, and the same holds for multi-qubit $U$ with several Bell pairs. Applied to encoded blocks, this reduces
fault-tolerant implementation of $U$ to fault-tolerant preparation of the encoded resource state.

## Depends on

- [Unitary evolution and elementary gates](../../quantum-foundations/unitary-evolution-and-elementary-gates.md)
- [Measurements: POVMs, projective measurements and the Born rule](../../quantum-foundations/measurements-povms-projective-measurements-and-the-born-rule.md)

## Proof depends on

- [Quantum teleportation](../../quantum-foundations/quantum-teleportation.md)
- [Clifford hierarchy](../clifford-group/clifford-hierarchy.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5 and Figure 5 ("he should do the gate $U Q U^\dagger$", the sets $C_k$).
- D. Gottesman and I. L. Chuang, *Demonstrating the viability of universal quantum computation using teleportation and single-qubit operations*, Nature 402 (1999), 390–393, arXiv:quant-ph/9908010.
