# Measurements: POVMs, projective measurements and the Born rule

Let $\Gamma$ be a finite set of outcomes. A *positive operator-valued measure* (POVM) on $\mathbb{C}^\Sigma$ with
outcomes $\Gamma$ is a family $(E_a)_{a \in \Gamma}$ of positive semidefinite operators on $\mathbb{C}^\Sigma$ with
$\sum_{a \in \Gamma} E_a = I$. By the *Born rule*, measuring a system in the [state](quantum-states-pure-states-and-density-operators.md)
$\rho$ gives outcome $a$ with probability $\operatorname{Tr}(E_a \rho)$, which is $\langle \psi | E_a | \psi \rangle$ for a
pure state $\psi$; these numbers are nonnegative and sum to $1$.

A *projective measurement* is a POVM $(P_a)_{a \in \Gamma}$ whose elements are orthogonal projectors; then
$P_a P_b = 0$ for $a \ne b$. When outcome $a$ occurs, with probability $p_a = \operatorname{Tr}(P_a \rho) > 0$, the state
becomes $P_a \rho P_a / p_a$, for a pure state $P_a \psi / \lVert P_a \psi \rVert$. Measuring in an orthonormal basis
$(e_a)_{a \in \Gamma}$ is the projective measurement with $P_a = |e_a\rangle\langle e_a|$, which gives outcome $a$ with
probability $|\langle e_a, \psi \rangle|^2$; the measurement in the computational basis takes the standard basis. A
projective measurement with distinct real outcomes $\lambda_a$ is recorded by the Hermitian operator, or observable,
$M = \sum_a \lambda_a P_a$, and the expected outcome is $\operatorname{Tr}(M \rho)$. On a part of a composite system the
measurement acts by $E_a \otimes I$.

## Depends on

- [Quantum states: pure states and density operators](quantum-states-pure-states-and-density-operators.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 1.2.2 (measurement in the computational basis, Born's rule, projective measurement, observables, POVM) and Section 15.1 (measurement of a mixed state: "the probability to see outcome $i$ is given by $p_i = \mathrm{Tr}(P_i \rho)$ ... the state collapses to $P_i \rho P_i / p_i$").
- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 4.2, Definition 4.2.1 (POVM).
