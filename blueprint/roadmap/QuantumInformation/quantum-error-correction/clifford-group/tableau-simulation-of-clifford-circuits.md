# Tableau simulation of Clifford circuits

A state of $n$ qubits obtained from $|0\rangle^{\otimes n}$ by CNOT, Hadamard and phase gates and computational-basis
measurements is a [stabilizer state](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md),
and it can be represented by a tableau of $2n$ rows of $2n + 1$ bits each: the $n$ stabilizer generators and $n$
"destabilizer" Pauli operators that together with them generate the Pauli group modulo scalar phases (their binary labels are independent, so a product of rows equal to a
scalar uses each row an even number of times and reduces to $\pm I$ by the real commutation signs; it cannot be $iI$,
although Hermitian Paulis in general can multiply to $iI$, as $XYZ = iI$ shows), each row holding the binary vector
$(x, z)$ of a Pauli operator and its sign bit. The tableau algorithm of Aaronson and Gottesman updates this representation
exactly: a CNOT, Hadamard or phase gate costs $O(n)$ bit operations, and a measurement of one qubit, whose outcome is
random with probability $1/2$ each or determined by the state, costs $O(n^2)$ bit operations, including the update of the
state after a random outcome. The representation keeps the invariants that the stabilizer rows generate the stabilizer of
the state, all $2n$ rows generate the Pauli group modulo phases, the destabilizer rows commute pairwise, row $h$ anticommutes with row
$h + n$, and row $i$ commutes with row $h + n$ for $i \ne h$.

## Depends on

- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
- [Positive-operator-valued measurements and the Born rule](../../quantum-operations/povms-and-measurement-readout/povm-and-born-rule.md)

## Proof depends on

- [Conjugation of Pauli operators by $H$, $S$ and CNOT](conjugation-of-pauli-operators-by-h-s-and-cnot.md)
- [Stabilizer measurement rule](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-measurement-rule.md)
- [Pauli operators commute exactly when their symplectic product vanishes](../stabilizer-formalism/pauli-operators-commute-iff-symplectic-product-vanishes.md)

## Sources

- S. Aaronson and D. Gottesman, *Improved simulation of stabilizer circuits*, Phys. Rev. A 70 (2004), 052328, arXiv:quant-ph/0406196, Section III (the tableau, the rowsum operation, the update rules for CNOT, Hadamard, phase and measurement, "only $O(n)$ time for each gate", "updating the state after the measurement takes $O(n^2)$") and Proposition 3.
