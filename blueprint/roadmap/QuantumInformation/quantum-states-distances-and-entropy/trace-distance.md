# Trace distance

The trace norm of an operator $X$ on $\mathbb{C}^\Sigma$ is $\lVert X \rVert_1 = \operatorname{Tr} \sqrt{X^* X}$, the sum of
the singular values of $X$. The *trace distance* between
[density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md) $\rho$ and $\sigma$ is

$$T(\rho, \sigma) = \tfrac12 \lVert \rho - \sigma \rVert_1 ,$$

which is half the sum of the absolute values of the eigenvalues of the Hermitian operator $\rho - \sigma$. It is a metric
on $\mathcal{D}(\mathbb{C}^\Sigma)$ with $0 \le T(\rho, \sigma) \le 1$, and $T(\rho, \sigma) = 0$ exactly when
$\rho = \sigma$. Some authors use $\lVert \rho - \sigma \rVert_1$ without the factor $\tfrac12$.

## Depends on

- [Quantum states: pure states and density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 9.1, Definition 9.1.2 and the bounds (9.22)–(9.23), with the normalized trace distance $\tfrac12 \lVert \rho - \sigma \rVert_1$.
