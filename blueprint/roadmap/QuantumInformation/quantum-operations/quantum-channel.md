# Quantum channel

For finite sets $\Sigma, \Gamma$ let $L(\mathbb{C}^\Sigma)$ be the space of linear operators on $\mathbb{C}^\Sigma$. A linear
map $\Phi : L(\mathbb{C}^\Sigma) \to L(\mathbb{C}^\Gamma)$ is *positive* if it maps positive semidefinite operators to
positive semidefinite operators, *completely positive* if $\mathrm{id}_{L(\mathbb{C}^k)} \otimes \Phi$ is positive for every
$k \ge 1$, and *trace preserving* if $\operatorname{Tr} \Phi(X) = \operatorname{Tr} X$ for all $X$. A *quantum channel* is a
completely positive, trace-preserving linear map.

A channel maps [density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md) to density
operators, and so does $\mathrm{id} \otimes \Phi$ on any larger system. Examples are the unitary channel
$\rho \mapsto U \rho U^*$, the partial trace, the preparation of a fixed state, and the Pauli channel
$\rho \mapsto \sum_{P} p_P\, P \rho P^{*}$ over Pauli operators $P$ with probabilities $p_P$ (for the Hermitian tensor products
of $I, X, Y, Z$ this is $P \rho P$; for $P = iI$ the map $\rho \mapsto P \rho P = -\rho$ is not a channel).

## Depends on

- [Quantum states: pure states and density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 4.4, Definitions 4.4.2 (completely positive map) and 4.4.3 (quantum channel), Criteria 4.4.1–4.4.3.
