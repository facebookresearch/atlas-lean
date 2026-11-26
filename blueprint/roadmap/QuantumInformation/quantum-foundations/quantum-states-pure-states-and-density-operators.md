# Quantum states: pure states and density operators

Let $\Sigma$ be a finite nonempty set and $\mathbb{C}^\Sigma$ the complex Euclidean space with its standard inner product.
A *pure state* of the system with classical states $\Sigma$ is a unit vector $\psi \in \mathbb{C}^\Sigma$; two unit vectors
that differ by a global phase, $\psi$ and $e^{i\theta}\psi$, describe the same physical state. A *density operator*, or
*mixed state*, on $\mathbb{C}^\Sigma$ is a positive semidefinite operator $\rho$ on $\mathbb{C}^\Sigma$ with
$\operatorname{Tr} \rho = 1$; the set $\mathcal{D}(\mathbb{C}^\Sigma)$ of density operators is convex.

The pure state $\psi$ has density operator $|\psi\rangle\langle\psi|$, which does not depend on the global phase. An
ensemble of pure states $\psi_x$ chosen with probabilities $p_x \ge 0$, $\sum_x p_x = 1$, has density operator
$\rho = \sum_x p_x |\psi_x\rangle\langle\psi_x|$, and every density operator arises this way, for instance from its spectral
decomposition, whose eigenvalues form a probability distribution. A density operator is the density operator of a pure
state exactly when it has rank one. The state space of a system made of parts with classical states $\Sigma_A$ and
$\Sigma_B$ is $\mathbb{C}^{\Sigma_A} \otimes \mathbb{C}^{\Sigma_B} = \mathbb{C}^{\Sigma_A \times \Sigma_B}$; an $n$-qubit
system has $\Sigma = \{0, 1\}^n$.

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 4.1, Definitions 4.1.2 (density operator of an ensemble) and 4.1.3 (density operator as the state), Exercise 4.1.8 (convexity).
- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, Section 1.2.1 (pure states, tensor products) and Section 15.1 (mixed states as density matrices; "the set of density matrices is exactly the set of positive semidefinite (psd) matrices of trace 1. A mixed state is pure if, and only if, it has rank 1").
