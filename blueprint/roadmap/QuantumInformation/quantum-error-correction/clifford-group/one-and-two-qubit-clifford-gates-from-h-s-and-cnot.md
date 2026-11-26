# One- and two-qubit Clifford gates are products of $H$, $S$ and CNOT

Every one-qubit [Clifford unitary](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)
is, up to a global phase, a product of Hadamard gates $H$ and phase gates $S = \operatorname{diag}(1, i)$: conjugation by
$H$ exchanges $X$ and $Z$, conjugation by $S$ exchanges $X$ and $Y$ up to sign, and together they induce every permutation
of $X, Y, Z$ with every compatible choice of signs. Every two-qubit Clifford unitary is, up to a global phase, a product of
one-qubit Clifford unitaries and one of the four operations: the identity, a CNOT, the swap, or a CNOT followed by the
swap; and the swap is the product of three CNOTs, alternating in direction. Hence every one- and two-qubit Clifford
unitary is, up to phase, a product of $H$, $S$ and CNOT.

Gottesman's proof sorts the two-qubit case by the image of $X \otimes I$, which up to one-qubit Clifford gates is
$X \otimes I$, $I \otimes X$ or $X \otimes X$, and then by the images of $I \otimes X$, $Z \otimes I$ and $I \otimes Z$
allowed by the commutation relations; a unitary is fixed up to phase by these images.

## Depends on

- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)

## Proof depends on

- [Conjugation of Pauli operators by $H$, $S$ and CNOT](conjugation-of-pauli-operators-by-h-s-and-cnot.md)
- [A unitary is determined up to phase by its conjugation action on Pauli operators](unitary-determined-up-to-phase-by-conjugation-of-paulis.md)

## Sources

- D. Gottesman, *Stabilizer codes and quantum error correction*, PhD thesis, California Institute of Technology (1997), arXiv:quant-ph/9705052, Section 5.3, equations (5.5)–(5.10) ($R$ and $P$ "generate all possible permutations of $\sigma_x$, $\sigma_y$, and $\sigma_z$"), and Section 5.6, the case analysis ending "the only possible two-qubit operations in $N(G)$ are the identity, a CNOT, a swap, or a CNOT followed by a swap" and Figure 5.2.
