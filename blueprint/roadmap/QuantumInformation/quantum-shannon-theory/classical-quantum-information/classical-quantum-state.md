# Classical-quantum states

Let $X$ be a finite set, $p$ a probability distribution on $X$ and $(\rho_x)_{x\in X}$ density matrices on $\mathbb{C}^\iota$. The *classical-quantum state* with quantum register first is the block-diagonal matrix

$$
\rho_{QX} = \sum_{x\in X} p(x)\,\rho_x\otimes|x\rangle\langle x| \quad\text{on } \mathbb{C}^\iota\otimes\mathbb{C}^X .
$$

It is a density matrix; its quantum marginal is the average state $\bar\rho = \operatorname{Tr}_X\rho_{QX} = \sum_x p(x)\rho_x$ and its classical marginal is $\operatorname{Tr}_Q\rho_{QX} = \operatorname{diag}(p)$. Its support is contained in that of another classical-quantum state $\sigma_{QX} = \sum_x q(x)\sigma_x\otimes|x\rangle\langle x|$ iff for every $x$ with $p(x) > 0$ one has $q(x) > 0$ and $\operatorname{supp}\rho_x\subseteq\operatorname{supp}\sigma_x$.

## Depends on

- [Density matrices, pure states and reduced states](../../quantum-states-distances-and-entropy/density-matrices-and-fidelity/density-matrices-and-reduced-states.md)
- [Partial trace over the first factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-left.md)
- [Partial trace over the second factor](../../../LinearAlgebra/linear-maps-and-duality/partial-trace/partial-trace-right.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
- J. Watrous, "The Theory of Quantum Information", Cambridge University Press, 2018.
