# Positive-operator-valued measurements and the Born rule

A *POVM* with finite outcome set $A$ on $\mathbb{C}^\iota$ is a family of positive semidefinite matrices $(E_a)_{a\in A}$ (effects) with $\sum_a E_a = I$; it is *projective* if every $E_a$ is idempotent. Measuring a density matrix $\rho$ yields outcome $a$ with probability $\Pr[a] = \operatorname{Tr}(E_a\rho)$, which for a pure state $|\psi\rangle\langle\psi|$ is $\langle\psi, E_a\psi\rangle$; these probabilities form a distribution, are affine in $\rho$, and for the computational-basis POVM $E_x = |x\rangle\langle x|$ read the diagonal of $\rho$. Standard operations: *post-processing* by $f:A\to B$ has effects $\sum_{a: f(a) = b}E_a$ and pushes the outcome law forward; the *product* of POVMs on two factors has effects $E_a\otimes F_b$; a classical random choice of POVM with law $\mu$ has effects $\sum_q \mu(q)E^q_a$. For a projective readout $\Pi_y$ the unnormalized post-measurement branch is $\Pi_y\rho\,\Pi_y$, of trace $\Pr[y]$.

A *$\pm1$ observable* is a Hermitian $O$ with $O^2 = I$; it corresponds to the projective two-outcome measurement with effects $(I\pm O)/2$. Conversely every two-outcome POVM has observable $O = E_0 - E_1$, which satisfies $O^2\le I$ because $I - O^2 = 4E_0(I - E_0)$.

## Depends on

- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Born rule normalization in a unitary measurement basis](../../../Physics/quantum-mechanics/postulates-of-finite-dimensional-quantum-mechani/sum-born-prob-unitary-orthonormal-basis.md)

## Sources

- R. Cleve, P. Hoyer, B. Toner and J. Watrous, "Consequences and limits of nonlocal strategies", Proceedings of the 19th IEEE Conference on Computational Complexity, 236-249, 2004.
- R. de Wolf, "Quantum Computing: Lecture Notes", arXiv:1907.09415, 2019.
- M. A. Nielsen and I. L. Chuang, "Quantum Computation and Quantum Information: 10th Anniversary Edition", Cambridge University Press, 2010.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
