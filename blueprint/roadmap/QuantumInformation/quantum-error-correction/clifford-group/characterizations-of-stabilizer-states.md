# Characterizations of stabilizer states

For an $n$-qubit pure state $|\psi\rangle$ the following are equivalent:

1. $|\psi\rangle$ can be obtained from $|0\rangle^{\otimes n}$ by CNOT, Hadamard and phase gates;
2. $|\psi\rangle$ can be obtained from $|0\rangle^{\otimes n}$ by CNOT, Hadamard and phase gates and computational-basis
   measurements;
3. $|\psi\rangle$ is stabilized by exactly $2^n$ elements of the [Pauli group](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md);
4. $|\psi\rangle$ is determined, up to a global phase, by the group of Pauli operators that stabilize it.

States with these properties are exactly the
[stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md).

## Depends on

- [The Pauli group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-on-n-qubits.md)
- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Proof depends on

- [Canonical form of Clifford circuits](canonical-form-of-clifford-circuits.md)
- [Stabilizer measurement rule](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-measurement-rule.md)
- [Dimension of a stabilizer code](../finrank-stabilizer-code.md)

## Sources

- S. Aaronson and D. Gottesman, *Improved simulation of stabilizer circuits*, Phys. Rev. A 70 (2004), 052328, arXiv:quant-ph/0406196, Section II, Theorem 1 (stated there with references to earlier work).
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 20.2 (Clifford circuits map stabilizer states to stabilizer states).
