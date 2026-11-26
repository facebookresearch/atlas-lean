# Gaussian-pattern maximum operator norm and minimum over spins

Use the [Gaussian-pattern model and function $L_\alpha$](gaussian-pattern-pressure.md). There exist $e_+\ge0$ and $e_-\le0$ with $L_\alpha(\beta)/\beta\to e_+$ and $L_\alpha(-\beta)/\beta\to e_-$ as $\beta\to+\infty$. Then

$$
N^{-1}\|Z_N^{\mathsf T}\|_{\ell^\infty_N\to\ell^2}\ \longrightarrow\ \sqrt{2e_+},\qquad
N^{-1}\min_{\sigma\in\{-1,1\}^N}\|Z_N^{\mathsf T}\sigma\|_2\ \longrightarrow\ \sqrt{-2e_-}
$$

both in measure and in $L^1$. The first norm uses the product supremum norm on the domain; it is not the Euclidean spectral norm.

**Conventions.** Use Gaussian patterns, the signed normalized ground energies, the induced operator norm with the supremum norm on the domain, and the finite spin minimum.

## Depends on

- [Invariant Ising pressure with rectangular Gaussian patterns](gaussian-pattern-pressure.md)

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [Gaussian-pattern ground limits with either sign](gaussian-pattern-ground-limit.md)

## Expansion

Identify the supremum over the unit cube with the maximum over its vertices using convexity. The negative-sign ground state gives the squared minimum. Justify the real square-root passage and the two $L^1$ conclusions at zero as well as positive limits.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L471-L490)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L234-L280)
