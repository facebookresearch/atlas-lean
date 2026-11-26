# Positive-temperature invariant Ising pressure with no outliers

Use the [normalized zero-field model](zero-field-pressure-limit.md) with measurable right Haar $U_N$ and deterministic eigenvalues whose empirical spectral laws tend weakly to $\nu$ supported in $[a,b]$ with both endpoints in its support. Assume for every $\epsilon>0$ that eventually all eigenvalues belong to $[a-\epsilon,b+\epsilon]$. For each $\beta>0$, replace every eigenvalue by $\beta\lambda_{Ni}$ in the pressure. The resulting expected pressure, and the pressure almost surely, converge to the real projection of $V((x\mapsto\beta x)_*\nu,\beta b)$. The limit here is the scaled log pressure, not divided by $\beta$.

## Depends on

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)
- [Normalized pressure and explicit spectral variational functional](zero-field-pressure-limit.md)

## Proof depends on

- [The spectral-extreme pressure theorem](zero-field-pressure-limit.md)

## Expansion

Use weak convergence and positive mass in neighborhoods of support endpoints, together with the no-outlier condition, to obtain the extreme eigenvalue limits. Transport the empirical law, support endpoints, and energy under multiplication by the fixed positive $\beta$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L322-L338)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
