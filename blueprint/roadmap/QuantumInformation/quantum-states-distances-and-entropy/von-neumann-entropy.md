# Von Neumann entropy

The *von Neumann entropy* of a [density operator](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)
$\rho$ on $\mathbb{C}^\Sigma$ is

$$H(\rho) = -\operatorname{Tr}(\rho \log \rho) = -\sum_{i} \lambda_i \log \lambda_i ,$$

where $\lambda_1, \dots, \lambda_{|\Sigma|}$ are the eigenvalues of $\rho$, with $0 \log 0 = 0$, and the logarithm is to
base $2$ unless stated otherwise. It is the [Shannon entropy](../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
of the spectrum of $\rho$, it satisfies $0 \le H(\rho) \le \log |\Sigma|$, it vanishes exactly on pure states, and it is
invariant under $\rho \mapsto U \rho U^*$. For a state $\rho_{AB}$ of a composite system, $H(A)$ denotes the entropy of the
reduced state $\rho_A$.

## Depends on

- [Quantum states: pure states and density operators](../quantum-foundations/quantum-states-pure-states-and-density-operators.md)
- [Shannon entropy](../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Sources

- M. M. Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8 (2019); also *Quantum Information Theory*, 2nd ed., Cambridge University Press, 2017, Section 11.1, Definition 11.1.1 and Exercise 11.1.1 (entropy of the eigenvalue distribution).
