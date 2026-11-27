# Polynomial-time uniform quantum circuit and verifier families

A *polynomial-time uniform family of quantum circuits* assigns to each input length $n$ a register width $m(n)\ge n$ and a list of Hadamard–Toffoli gate codes, both computed from $1^n$ by a polynomial-time Turing machine; on input $x$ the circuit runs on $|x0^{m-n}\rangle$ and accepts when a designated qubit reads $1$. A *uniform family of quantum verifiers* additionally has a witness length $q(n)$ (computed in polynomial time) and runs on $|x\rangle\otimes|\psi\rangle\otimes|0\cdots0\rangle$ for a witness state $\psi$ on $q(n)$ qubits. The *acceptance operator* $Q_x=B_x^\dagger B_x$, where $B_x$ restricts the final state to accepting outcomes, is positive semidefinite with $\langle\psi|Q_x|\psi\rangle$ equal to the acceptance probability, so the maximal acceptance probability is the largest eigenvalue of $Q_x$.

## Depends on

- [Quantum circuits over the Hadamard–Toffoli gate set](hadamard-toffoli-quantum-circuits.md)
- [Log-space uniform circuit families](../../../complexity-classes/time-and-space-complexity-classes/uniform-circuit-family.md)
- [QMA for promise problems](../../local-hamiltonian-problem/qmapromise.md)

## Sources

- John Watrous, "Quantum Computational Complexity", in Encyclopedia of Complexity and Systems Science, Springer, 7174–7201, 2009 (arXiv:0804.3401).
- Chris Marriott, John Watrous, "Quantum Arthur–Merlin Games", Computational Complexity 14(2), 122–152, 2005.
- A. Yu. Kitaev, A. H. Shen and M. N. Vyalyi, "Classical and Quantum Computation", Graduate Studies in Mathematics 47, American Mathematical Society, 2002, Chapter 14 (QMA).
- Ronald de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019 (lecture notes; supplementary pointer).
