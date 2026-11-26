# Polynomial-time uniform quantum circuit and verifier families

A *polynomial-time uniform family of quantum circuits* assigns to each input length $n$ a register width $m(n)\ge n$ and a list of Hadamard–Toffoli gate codes, both computed from $1^n$ by a polynomial-time Turing machine; on input $x$ the circuit runs on $|x0^{m-n}\rangle$ and accepts when a designated qubit reads $1$. A *uniform family of quantum verifiers* additionally has a witness length $q(n)$ (computed in polynomial time) and runs on $|x\rangle\otimes|\psi\rangle\otimes|0\cdots0\rangle$ for a witness state $\psi$ on $q(n)$ qubits. The *acceptance operator* $Q_x=B_x^\dagger B_x$, where $B_x$ restricts the final state to accepting outcomes, is positive semidefinite with $\langle\psi|Q_x|\psi\rangle$ equal to the acceptance probability, so the maximal acceptance probability is the largest eigenvalue of $Q_x$.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Log-space uniform circuit families](../../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)
- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)

## Sources

- John Watrous, "Quantum Computational Complexity", 2008.
- Chris Marriott, John Watrous, "Quantum Arthur–Merlin Games", Computational Complexity, 2005.
- Ronald de Wolf, "Quantum Computing: Lecture Notes", 2019.
