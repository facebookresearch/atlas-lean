# Invariant Ising pressure in L1 under uniform integrability

Take the [same random eigenvalue and zero-field conditional Haar pressure model with empirical convergence and no-outlier excess in probability](random-spectrum-pressure-in-measure.md). If the family $Y_N$ for positive sizes is uniformly integrable in $L^1$, then it converges in measure and in $L^1$ to the real projection of $V(\nu,b)$, and its expectations converge to that number.

Uniform integrability is a separate assumption on the sequence of random pressures, not on the spectral laws.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)
- [The random-spectrum hypotheses](random-spectrum-pressure-in-measure.md)

## Proof depends on

- [Random-spectrum convergence in measure](random-spectrum-pressure-in-measure.md)

## Proof outline

Apply the uniform-integrability convergence theorem on the probability space to the just-identified constant limit, then use the absolute mean difference bounded by the $L^1$ difference. Retain all three conclusions.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L377-L401)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
