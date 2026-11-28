# Gottesman–Knill theorem

Fix a classical algorithm, the controller, that given the description of a circuit and the outcomes of its earlier
measurements outputs the next gate or measurement in time polynomial in the size of the description. There is a
classical polynomial-time algorithm that, given an $n$-qubit circuit of Hadamard, phase and CNOT gates and
computational-basis measurements applied to $|0^n\rangle$, whose later gates of the same kinds are chosen from the earlier
outcomes by this controller, samples exactly from the joint distribution of its measurement outcomes. Fixing one
controller is one way to obtain a common polynomial bound (explicitly supplied Boolean control circuits, evaluated within
a polynomial in their size, are another): separate controllers, each polynomial in its own history, need not have one,
and a short one can hard-code an instance of an exponential-time problem and reveal its answer through a deterministic
final measurement.

## Depends on

- [Positive-operator-valued measurements and the Born rule](../../../QuantumInformation/quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)
- [The Clifford group on $n$ qubits](clifford-group-on-n-qubits.md)

## Proof depends on

- [Stabilizer measurement rule](stabilizer-measurement-rule.md)
- [Tableau simulation of Clifford circuits](../../../QuantumInformation/quantum-error-correction/clifford-group/tableau-simulation-of-clifford-circuits.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §20.3, Theorem 6. <https://arxiv.org/pdf/1907.09415v6>
