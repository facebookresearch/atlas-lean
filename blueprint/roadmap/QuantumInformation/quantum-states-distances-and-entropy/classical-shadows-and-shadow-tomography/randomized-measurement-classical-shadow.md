# Classical shadows from randomized measurements

Let $\mathcal{U}$ be a distribution over unitaries on $n$ qubits, either the uniform distribution over the $n$-qubit Clifford group (*Clifford shadows*) or the product of independent uniformly random single-qubit Clifford gates (*Pauli shadows*). Measuring $U\rho U^\dagger$ in the computational basis with outcome $b \in \{0,1\}^n$ defines the *measurement channel*

$$
\mathcal{M}(\rho) = \mathbb{E}_{U \sim \mathcal{U}} \sum_{b} \langle b | U\rho U^\dagger | b\rangle \, U^\dagger |b\rangle\langle b| U .
$$

When $\mathcal{M}$ is invertible, the *classical shadow snapshot* is $\hat\rho = \mathcal{M}^{-1}(U^\dagger|b\rangle\langle b|U)$, a random Hermitian operator with $\mathbb{E}[\hat\rho] = \rho$, stored efficiently as the pair $(U, b)$.

## Depends on

- [The shadow tomography problem](shadow-tomography-problem.md)
- [Pauli group, Clifford group and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/pauli-group-clifford-group-and-stabilizer-states.md)

## Sources

- Hsin-Yuan Huang, Richard Kueng, John Preskill, "Predicting many properties of a quantum system from very few measurements", Nature Physics 16 (2020); arXiv:2002.08953.
