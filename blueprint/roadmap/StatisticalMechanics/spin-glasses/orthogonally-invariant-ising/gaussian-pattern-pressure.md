# Invariant Ising pressure with rectangular Gaussian patterns

Let $\alpha>0$, and for each $N\ge1$ let $Z_N$ be a measurable $N\times\lfloor\alpha N\rfloor$ standard Gaussian matrix on a common probability space; no cross-size independence is needed. Fix $c\in\mathbb R$. For spins $\sigma\in\{-1,1\}^N$, the normalized log-partition pressure uses energy $c\|Z_N^{\mathsf T}\sigma\|_2^2/(2N)$ and the uniform spin average, followed by division by $N$.

Let $l=(1-\sqrt\alpha)^2$, $u=(1+\sqrt\alpha)^2$, and $l_0=0$ if $\alpha\le1$, $l_0=l$ otherwise. The Marchenko–Pastur law $\mu_\alpha$ has atom $(1-\alpha)_+$ at $0$ and density $\sqrt{(u-x)(x-l)}/(2\pi x)$ on $[l,u]$ (endpoint values do not affect the measure). Write $L_\alpha(c)$ for the real projection of $V((x\mapsto cx)_*\mu_\alpha,\max(cl_0,cu))$ with the [spectral functional](spectral-and-field-step-functionals.md). The random pressure converges in measure and in $L^1$ to $L_\alpha(c)$, and its expectation converges to the same number.

**Conventions.** Use the exact rectangular Gaussian aspect ratio with natural floor, the Gaussian Gram matrix, and the scaled Marchenko–Pastur spectral law with its upper edge chosen according to the sign of $c$.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [The random-spectrum pressure comparison](random-spectrum-pressure-in-measure.md)
- [The uniform-integrability upgrade](random-spectrum-pressure-l1.md)

Also use Gaussian invariance conditional on the eigenvalues, empirical law and extreme spectral convergence, and moment control of the Gaussian Gram norm.

## Expansion

Verify the Haar orbit law, including rank deficiency when the number of columns is smaller than $N$, and transfer the spectral laws through the signed scaling. Treat $c=0$ and negative $c$ without replacing the upper spectrum edge by $cu$ unconditionally.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L443-L456)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
