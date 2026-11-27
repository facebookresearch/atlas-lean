# Clifford computations with mixtures of stabilizer states are classically simulable

Let $\rho$ be a one-qubit state with Bloch vector $(\rho_x, \rho_y, \rho_z)$, $\rho = \tfrac12(I + \rho_x X + \rho_y Y + \rho_z Z)$,
such that $|\rho_x| + |\rho_y| + |\rho_z| \le 1$, that is, the vector lies in the octahedron with vertices
$(\pm 1, 0, 0)$, $(0, \pm 1, 0)$, $(0, 0, \pm 1)$. Then every adaptive computation that prepares $|0\rangle$ and independent copies of
$\rho$ (the state $\rho^{\otimes m}$), applies Clifford unitaries, measures one-qubit Pauli operators and chooses later
operations as functions of earlier outcomes computed by an efficient classical algorithm can be simulated efficiently on a
classical probabilistic computer. The efficiency of the classical control is needed: otherwise the controller could compute
a hard function itself and report it by choosing $I$ or $X$.

Proof: $\rho$ is a convex combination of the six one-qubit stabilizer states (the eigenstates of $X$, $Y$, $Z$), which can
be prepared, independently for each copy, by sampling with the corresponding weights and then preparing a stabilizer state; the whole computation is
then a stabilizer computation, covered by the Gottesman–Knill theorem. Magic states lie outside the octahedron, which is
why they can add computational power.

## Depends on

- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Proof depends on

- [Gottesman–Knill theorem](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/gottesmanknill-theorem.md)

## Background

- [Magic states](magic-state.md)

## Sources

- S. Bravyi and A. Kitaev, *Universal quantum computation with ideal Clifford gates and noisy ancillas*, Phys. Rev. A 71 (2005), 022316, arXiv:quant-ph/0403025, Section I, Theorem 1 and the paragraph before it.
