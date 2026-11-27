# Gaussian-pattern ground energy and the zero-temperature pressure limit

Use the [Gaussian patterns and $L_\alpha$ normalization](gaussian-pattern-pressure.md) for $\alpha>0$. For every real $\epsilon$, there exists a real $e$ such that the maximum over $\sigma\in\{-1,1\}^N$ of $\epsilon\|Z_N^{\mathsf T}\sigma\|_2^2/(2N^2)$ converges in measure and in $L^1$ to $e$, and the expected maximum converges to $e$. Also $L_\alpha(\epsilon\beta)/\beta\to e$ as $\beta\to+\infty$. When $\epsilon<0$ the maximum involves a minimum of the underlying squared norm, not the ordinary unsigned maximum.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)
- [Gaussian-pattern pressure and spectral limit](gaussian-pattern-pressure.md)

## Proof depends on

- [The positive-temperature Gaussian-pattern limit](gaussian-pattern-pressure.md)

## Expansion

Use the uniform $\log2/\beta$ bound between normalized log partition divided by $\beta$ and the ground-state maximum. Derive the limiting scalar first and treat convergence of expectations and the $L^1$ error with that same scalar, keeping the sign of $\epsilon$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L457-L470)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
