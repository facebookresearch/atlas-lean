# Divergence to a common reference and the product-reference bound

Let $\rho_{QX} = \sum_x p(x)\rho_x\otimes|x\rangle\langle x|$ with average state $\bar\rho$, and let $\sigma$ be a density matrix on $\mathbb{C}^\iota$. Then, as an identity in $[0,+\infty]$,

$$
\sum_x p(x)\,D(\rho_x\,\|\,\sigma) = I(Q:X)_\rho + D(\bar\rho\,\|\,\sigma).
$$

Consequently, for every probability distribution $q$ on $X$, $I(Q:X)_\rho \le D\big(\rho_{QX}\,\|\,\sum_x q(x)\,\sigma\otimes|x\rangle\langle x|\big)$.

## Proof sketch

When $\operatorname{supp}\bar\rho\subseteq\operatorname{supp}\sigma$, expand $\operatorname{Tr}\rho_x(\log\rho_x - \log\sigma) = \operatorname{Tr}\rho_x(\log\rho_x - \log\bar\rho) + \operatorname{Tr}\rho_x(\log\bar\rho-\log\sigma)$ and average over $p$; otherwise both sides are infinite. For the bound, the chain rule writes the right side as $D_{\mathrm{KL}}(p\|q) + \sum_x p(x) D(\rho_x\|\sigma)$, which by the identity and nonnegativity is at least $I(Q:X)$.

## Depends on

- [Classical-quantum states](classical-quantum-state.md)
- [Quantum mutual information](quantum-mutual-information.md)

## Proof depends on

- [Mutual information of a classical-quantum state](classical-quantum-mutual-information.md)
- [Relative-entropy chain rule for classical-quantum states](classical-quantum-relative-entropy-chain-rule.md)
- [Nonnegativity of quantum relative entropy for singular states (Klein's inequality)](../../quantum-states-distances-and-entropy/quantum-relative-entropy/relative-entropy-nonnegativity.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
