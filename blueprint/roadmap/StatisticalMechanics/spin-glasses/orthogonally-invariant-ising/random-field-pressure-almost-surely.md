# Almost-sure invariant Ising pressure with random spectral and field data

Let $\lambda_N,c_N,Y_N$ be measurable random eigenvalues, fields and real pressures. At each size require that the joint law of $(\lambda_N,c_N,Y_N)$ is the pushforward of the marginal data law times right Haar probability on $O(N)$ under $(\lambda,c,U)\mapsto(\lambda,c,P_N(c))$. Assume the [almost-sure spectral weak convergence and no-outlier hypotheses](random-spectrum-pressure-almost-surely.md) for a fixed compactly supported $\nu$ with endpoints $a,b$. Further assume first-moment-integrable $\xi$ and almost-sure convergence of the field empirical laws to $\xi$ in Wasserstein one. Then almost surely $Y_N\to V_{\rm mag}(\nu,b,\xi)$ as defined in the [magnetic formula](wasserstein-field-pressure-limit.md).

**Conventions.** Use the joint data and pressure law at each size, Haar rotation independent of the joint data in its product representation, and the fixed limiting spectral and field laws.

## Depends on

- [Almost-sure invariant Ising pressure for a random spectrum](random-spectrum-pressure-almost-surely.md)

- [Spectral and magnetic field-step functionals](spectral-and-field-step-functionals.md)

- [Rotated Ising pressure and spectral data](rotated-spin-pressure.md)

## Proof depends on

- [The deterministic Wasserstein-field pressure comparison](wasserstein-field-pressure-limit.md)

Haar concentration for the rotated quadratic term must work with the chosen finite field profile.

## Expansion

Use the pathwise data hypotheses to identify the conditional mean limit, and conditional concentration plus summability to transfer to each actual pressure realization. Do not require the actual fields and eigenvalues to be independent of one another.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/InvariantIsing.lean#L421-L442)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/234.md)
- [Accompanying manuscript: All-temperature pressure for orthogonally invariant Ising spin glasses](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/All-temperature-pressure-for-orthogonally-invariant-Ising-spin-glasses-September-25-2026/paper.pdf)
