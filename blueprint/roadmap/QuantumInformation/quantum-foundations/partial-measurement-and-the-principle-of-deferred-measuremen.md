# Partial measurement and the principle of deferred measurement

Consider a circuit that measures a register $A$ in the computational basis at some point and later applies unitaries
classically controlled on the outcome, where $A$ is not acted on again after the measurement except as a control.
Replace each classical control by the corresponding quantum-controlled unitary with $A$ as control, and measure $A$ in
the computational basis at the end. The two circuits give the same joint distribution of all measurement outcomes, and,
for every outcome sequence of positive probability, the same conditional state of the remaining registers. If the
original circuit reuses $A$ after the measurement, the outcome is first copied by CNOT into a fresh record register that
is never touched again, and the record register plays the role of $A$.

## Depends on

- [Unitary evolution and elementary gates](unitary-evolution-and-elementary-gates.md)
- [Positive-operator-valued measurements and the Born rule](../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Chapter 2, Exercise 8 (delaying every intermediate measurement to the end with one auxiliary qubit per measurement) and its hint in Appendix C (copy the qubit by a CNOT into a fresh qubit that is left alone until the end). <https://arxiv.org/pdf/1907.09415v6>
