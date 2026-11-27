# Classical shadows from randomized measurements

Let $\mathcal{U}$ be a distribution over unitaries on $n$ qubits, either the uniform distribution over the $n$-qubit Clifford group modulo global phases, that is over the projective Clifford group, with any representative of each class (*Clifford shadows*), or the product of independent uniformly random single-qubit Clifford gates modulo phase (*Pauli shadows*); the measurement channel below does not depend on the phases. Measuring $U\rho U^\dagger$ in the computational basis with outcome $b \in \{0,1\}^n$ defines the *measurement channel*

$$
\mathcal{M}(\rho) = \mathbb{E}_{U \sim \mathcal{U}} \sum_{b} \langle b | U\rho U^\dagger | b\rangle \, U^\dagger |b\rangle\langle b| U .
$$

When $\mathcal{M}$ is invertible, the *classical shadow snapshot* is $\hat\rho = \mathcal{M}^{-1}(U^\dagger|b\rangle\langle b|U)$, a random Hermitian operator with $\mathbb{E}[\hat\rho] = \rho$, stored efficiently as $b$ together with a tableau describing $U$ modulo phase.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [The Clifford group on $n$ qubits](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/clifford-group-on-n-qubits.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
