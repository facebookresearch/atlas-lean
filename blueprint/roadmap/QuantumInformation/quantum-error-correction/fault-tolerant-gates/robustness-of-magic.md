# Robustness of magic

Let $\mathcal{S}_n = \{\sigma_i\}$ be the finite set of density operators of the pure $n$-qubit
[stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md).
The *robustness of magic* of an $n$-qubit [state](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
$\rho$ is

$$\mathcal{R}(\rho) = \min \Big\{ \sum_i |x_i| \;:\; \rho = \sum_i x_i \sigma_i,\ x_i \in \mathbb{R} \Big\},$$

a linear program, since the stabilizer states span the Hermitian operators. Every decomposition has $\sum_i x_i = 1$, so
$\mathcal{R}(\rho) \ge 1$, with equality exactly for mixtures of stabilizer states. It is non-increasing under trace-preserving stabilizer operations, non-increasing on average under a stabilizer
measurement, $\sum_a p_a \mathcal{R}(\rho_a) \le \mathcal{R}(\rho)$ for outcome probabilities $p_a$ and post-measurement states
$\rho_a$, but not on each outcome separately (measuring the flag of an equal mixture of a flagged stabilizer state and a
flagged magic state $M$ yields $M$ on one outcome, while the input has robustness at most $(1 + \mathcal{R}(M))/2 < \mathcal{R}(M)$),
and submultiplicative, $\mathcal{R}(\rho_1 \otimes \rho_2) \le \mathcal{R}(\rho_1) \mathcal{R}(\rho_2)$.

## Depends on

- [Stabilizer groups and stabilizer states](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-groups-and-stabilizer-states.md)
- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)

## Proof depends on

- [Stabilizer measurement rule](../../../TheoryOfComputation/randomized-and-quantum-complexity/bounded-error-quantum-polynomial-time-bqp/stabilizer-measurement-rule.md): each branch of a Pauli measurement on a stabilizer state is a stabilizer state

## Sources

- M. Howard and E. Campbell, *Application of a resource theory for magic states to fault-tolerant quantum computing*, Phys. Rev. Lett. 118 (2017), 090501, arXiv:1609.07488, equations (1)–(4) and the discussion of the properties of the robustness of magic (proofs in the Supplementary Material).
