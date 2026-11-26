# Discrete SK ratio cutoff below inverse temperature one half

For $0\le\beta<1/2$, use zero-field Gibbs heat bath with independent Gaussian couplings of variance $\beta^2/n$. At each discrete attempt choose one site uniformly and resample conditionally (the transition is the identity for $n=0$). Let $t_W(a)$ be the least number of attempts at which the worst-start total-variation distance is at most $a$. For every $0<\varepsilon<1/2$ and $\eta>0$ the disorder probability of

$$
1+\eta < \frac{t_W(\varepsilon)}{t_W(1-\varepsilon)}
$$

tends to zero, taking the ratio in the reals. For all sufficiently large $n$ the denominator is positive for every disorder realization, not merely with high probability. There is no claimed location of cutoff, no continuous-time assertion and no larger inverse-temperature range.

**Conventions.** Use the worst-start heat bath with two error thresholds and the Gaussian SK law under the stated normalization.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

A high-temperature contraction/variance bound strong enough to compare the two mixing quantiles at the discrete update scale; a positive spectral gap alone is not a ratio-cutoff proof.

## Expansion

Show $t_W(1-\varepsilon)>0$ at sufficiently large sizes from the point mass at a state of Gibbs probability at most $2^{-n}$. Next control the high-temperature transition window relative to the denominator and quantify the bad-disorder probability. Retain the endpoint $\beta=0$.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKRatio.lean#L59-L69)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Cutoff throughout the high-temperature Sherrington–Kirkpatrick phase](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Cutoff-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/paper.pdf)
