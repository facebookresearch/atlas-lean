# The invariant Ising ground-state limit and its thermal characterization

Use the [same deterministic no-outlier and weak spectral hypotheses with Haar rotations](positive-temperature-pressure.md). There exists a real $M$ such that $N^{-1}\max_{\sigma\in\{-1,1\}^N}H_N(\sigma)$ converges to $M$ both in expectation and almost surely. The real projection of $V((x\mapsto\beta x)_*\nu,\beta b)$ divided by $\beta$ converges to the same $M$ as $\beta\to+\infty$.

**Conventions.** Use the zero-field Hamiltonian and the positive-temperature variational limit, with a normalized maximum and a separate inverse-temperature division for the latter.

## Depends on

- [Positive-temperature invariant Ising pressure with no outliers](positive-temperature-pressure.md)

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [Positive-temperature pressure](positive-temperature-pressure.md)

## Expansion

Use the uniform maximum versus normalized log-partition gap at most $\log 2/\beta$. Take a countable unbounded sequence of temperatures for simultaneous almost-sure pressure comparisons, and separately control expectation. Avoid taking a single exceptional event by intersecting an uncountable collection.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L339-L356)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
