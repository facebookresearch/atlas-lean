# High-temperature SK heat-bath Poincaré and gap bounds

Fix $0<\beta<1$. For each size $n$ use the [zero-field SK Gibbs model](gaussian-sk-heat-bath.md) with independent couplings of variance $\beta^2/n$, absorbing the inverse temperature into the couplings. Write $P_i f=\mathbb E_{\pi_W}(f\mid X_j,\ j\ne i)$ and $\mathcal E_W(f)=\sum_i\mathbb E_{\pi_W}(f-P_i f)^2$. There exists $C>0$ such that, with disorder probability tending to one, every real $f$ satisfies $\operatorname{Var}_{\pi_W} f\le C\mathcal E_W(f)$. With disorder probability tending to one the discrete gap, the infimum of $\mathcal E_W(f)/(n\operatorname{Var}_{\pi_W}f)$ over positive-variance tests, is at least $1/(Cn)$ with the same $C$.

**Conventions.** Use the finite Gibbs model, native conditional expectations, and the rate-one Dirichlet normalization rather than the averaged discrete normalization.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof outline

Uniform high-temperature disorder control of the Poincaré constant throughout $0<\beta<1$, not only deterministically small interaction norms. The gap implication uses the Rayleigh characterization.

Match edge indexing and Gaussian variance to the native SK law. Build the Poincaré argument through the critical threshold from below, then deduce the discrete spectral estimate by taking the infimum only over positive-variance functions. The finite-volume definitions with external fields are specialized to zero field in the result.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKHighTemperature.lean#L70-L72)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: A spectral gap throughout the high-temperature Sherrington–Kirkpatrick phase](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKHighTemperature.lean#L11-L62)
