# Every stabilizer state is local-Clifford equivalent to a graph state

For every $n$-qubit [stabilizer state](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
$|\psi\rangle$ there are a [graph state](graph-state.md) $|G\rangle$ on $n$ vertices and one-qubit Clifford unitaries
$U_1, \dots, U_n$ with $|\psi\rangle = (U_1 \otimes \cdots \otimes U_n) |G\rangle$ up to a global phase. Proof: write the
stabilizer generators as the columns of a $2n \times n$ matrix $\binom{Z}{X}$; a local Clifford operation,
here Hadamards on a suitable set of qubits, makes the $X$ block $X'$ invertible, and changing generators by $X'^{-1}$ gives
$\binom{Z' X'^{-1}}{I}$, where $Z' X'^{-1}$ is symmetric because the generators commute. Phase gates clear its diagonal,
and Pauli $Z$ gates fix the signs, so the result is the tableau of the graph state whose adjacency matrix is
$Z' X'^{-1}$ with zero diagonal.

## Depends on

- [Graph state](graph-state.md)
- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)
- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)

## Proof depends on

- [Pauli operators commute exactly when their symplectic product vanishes](pauli-operators-commute-iff-symplectic-product-vanishes.md)
- [Conjugation of Pauli operators by $H$, $S$ and CNOT](../clifford-group/conjugation-of-pauli-operators-by-h-s-and-cnot.md)

## Sources

- M. Van den Nest, J. Dehaene and B. De Moor, *Graphical description of the action of local Clifford transformations on graph states*, Phys. Rev. A 69 (2004), 022316, arXiv:quant-ph/0308151, Section III, Theorem 1 ("Each stabilizer state is equivalent to a graph state under local Clifford operations") and its proof; a special case of a result of Schlingemann for stabilizer codes on qudits.
