# Relative-entropy chain rule for classical-quantum states

Let $p,q$ be probability distributions on a finite set $X$ and $(\rho_x)$, $(\sigma_x)$ density matrices on $\mathbb{C}^\iota$. For the classical-quantum states $\rho_{QX} = \sum_x p(x)\rho_x\otimes|x\rangle\langle x|$ and $\sigma_{QX} = \sum_x q(x)\sigma_x\otimes|x\rangle\langle x|$,

$$
D(\rho_{QX}\,\|\,\sigma_{QX}) = D_{\mathrm{KL}}(p\,\|\,q) + \sum_{x} p(x)\, D(\rho_x\,\|\,\sigma_x),
$$

in nats, with $D_{\mathrm{KL}}(p\|q) = +\infty$ when $p\not\ll q$, and with a label of zero weight contributing $0$ even when its conditional divergence is infinite.

## Proof sketch

The support test is blockwise, so both sides are infinite together. On compatible supports the functional calculus acts blockwise: $\log(p(x)\rho_x) = \log p(x)\,\Pi_x + \log\rho_x$ on the support $\Pi_x$ of $\rho_x$, and similarly for $\sigma$. Taking the trace against $p(x)\rho_x$ in each block separates the classical log-likelihood ratio from the conditional quantum divergence.

## Depends on

- [Classical-quantum states](classical-quantum-state.md)
- [Support inclusion and Umegaki relative entropy](../../quantum-states-distances-and-entropy/quantum-relative-entropy/umegaki-relative-entropy.md)
- [Kullback–Leibler divergence on a finite space](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

- [Classical-quantum states](classical-quantum-state.md)

## Sources

- M. Bavarian, T. Vidick and H. Yuen, "Anchored Parallel Repetition for Nonlocal Games", SIAM Journal on Computing 51(2):214-253, 2022.
