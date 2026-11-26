# Almost-sure invariant Ising pressure for a random spectrum

Let the real pressures and finite eigenvalue arrays be measurable and satisfy the [joint-law conditional Haar premise](random-spectrum-pressure-in-measure.md). Suppose almost surely the empirical eigenvalue laws tend weakly to a fixed compactly supported $\nu$ with support in $[a,b]$ containing both endpoints. Suppose almost surely for every $\epsilon>0$ eventually all eigenvalues are in $[a-\epsilon,b+\epsilon]$. Then almost surely $Y_N$ tends to the real projection of $V(\nu,b)$. There is no independence assumption across sizes and no $L^1$ statement in this variant.

**Conventions.** Use the random spectral model and its single-size conditional Haar law. The almost-sure spectral hypotheses concern the full random sequence.

## Depends on

- [Invariant Ising pressure convergence in measure for random spectra](random-spectrum-pressure-in-measure.md)

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [Deterministic no-outlier pressure](positive-temperature-pressure.md)

Also use summably small conditional Haar deviation estimates, localized to bounded spectral data.

## Expansion

Use a deterministic spectral cap on the event that the data eventually stay in range. Transfer deviation bounds using each joint law and apply Borel–Cantelli; this works without independence across sizes. The mean pressure conditional on the realized spectrum is identified by the deterministic theorem.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L402-L420)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
