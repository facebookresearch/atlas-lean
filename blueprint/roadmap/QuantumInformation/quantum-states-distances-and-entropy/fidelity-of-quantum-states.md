# Fidelity of quantum states

The *fidelity* of [density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)
$\rho$ and $\sigma$ on $\mathbb{C}^\Sigma$ is

$$F(\rho, \sigma) = \big\lVert \sqrt{\rho} \sqrt{\sigma} \big\rVert_1 = \operatorname{Tr} \sqrt{\sqrt{\rho}\, \sigma \sqrt{\rho}} ,$$

where $\sqrt{\cdot}$ is the positive semidefinite square root and $\lVert \cdot \rVert_1$ the trace norm. It is symmetric,
$0 \le F(\rho, \sigma) \le 1$, and $F(\rho, \sigma) = 1$ exactly when $\rho = \sigma$. For pure states,
$F(|\psi\rangle\langle\psi|, |\varphi\rangle\langle\varphi|) = |\langle \psi, \varphi \rangle|$, and
$F(|\psi\rangle\langle\psi|, \sigma) = \sqrt{\langle \psi | \sigma | \psi \rangle}$. Some authors, including Wilde, call
the square $F(\rho, \sigma)^2$ the fidelity; this page and the Fuchs–van de Graaf inequalities use the unsquared form.

## Depends on

- [Quantum states: pure states and density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 9.2, Definitions 9.2.1 (pure-state fidelity $|\langle\psi|\varphi\rangle|^2$), 9.2.2 (expected fidelity) and 9.2.3 with equation (9.101), $F(\rho, \sigma) = \lVert \sqrt{\rho}\sqrt{\sigma} \rVert_1^2$ in the squared convention.
