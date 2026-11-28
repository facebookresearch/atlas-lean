# Clifford hierarchy

Fix $n \ge 1$ and let $\mathcal{P}_n$ be the $n$-qubit Pauli group. The levels of the Clifford hierarchy are the sets
of unitaries

$$\mathcal{C}^{(1)} = \mathcal{P}_n, \qquad
\mathcal{C}^{(k)} = \{ U \in U(2^n) : U Q U^{*} \in \mathcal{C}^{(k-1)} \text{ for all } Q \in \mathcal{P}_n \} \quad (k \ge 2).$$

So $\mathcal{C}^{(2)}$ is the Clifford group. For $k \ge 3$ the set $\mathcal{C}^{(k)}$ is not closed under
multiplication. The levels organise gate teleportation: teleporting a qubit through the ancilla
$(I \otimes U)(|00\rangle + |11\rangle)/\sqrt 2$, for a one-qubit $U$, applies $U$ up to a correction $U Q U^{*}$ for a Pauli outcome $Q$, which lies in
$\mathcal{C}^{(k-1)}$ when $U \in \mathcal{C}^{(k)}$; for $U$ in the third level the correction is a Clifford gate.

## Depends on

- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)
- [Quantum teleportation](../../quantum-foundations/quantum-teleportation.md)

## Sources

- D. Gottesman, *An introduction to quantum error correction and fault-tolerant quantum computation*, Proceedings of Symposia in Applied Mathematics 68 (2010), arXiv:0904.2557, Section 4.5 (the sets $C_k$).
