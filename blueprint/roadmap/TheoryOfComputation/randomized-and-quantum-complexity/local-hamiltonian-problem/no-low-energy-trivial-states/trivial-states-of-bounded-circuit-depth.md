# Circuit depth of a quantum state and trivial states

The *circuit depth* of an $n$-qubit state $\rho$ is the least $d$ such that $\rho = \mathrm{Tr}_{\mathsf{anc}}\big(U (|0\rangle\langle 0|^{\otimes (n + a)}) U^\dagger\big)$ for some number $a$ of ancilla qubits and a circuit $U$ of depth $d$ consisting of arbitrary two-qubit gates (no geometric locality assumed). A family of states is *trivial* if its circuit depth is bounded by a constant independent of $n$.

## Sources

- Anurag Anshu, Nikolas P. Breuckmann, Chinmay Nirkhe, "NLTS Hamiltonians from good quantum codes", STOC (2023); arXiv:2206.13228.
- Michael H. Freedman, Matthew B. Hastings, "Quantum systems on non-k-hyperfinite complexes: a generalization of classical statistical mechanics on expander graphs", Quantum Information and Computation 14 (2014); arXiv:1301.1363.
