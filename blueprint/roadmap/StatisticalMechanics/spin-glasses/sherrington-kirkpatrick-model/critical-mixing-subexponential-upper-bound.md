# Critical SK polynomial lower and subexponential upper mixing bounds

At inverse temperature one, under the [zero-field critical heat bath and worst-start $1/4$ times](gaussian-sk-heat-bath.md), for each fixed $\varepsilon>0$ the disorder probability of $n^{2/3-\varepsilon}\le t_c\le e^{\varepsilon n}$ tends to one. Separately, the disorder probability of $n^{5/3-\varepsilon}\le t_d\le e^{\varepsilon n}$ tends to one. Both laws use variance $1/n$ for each unordered coupling, and the continuous kernel updates at rate one per site.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

- [Critical mixing lower bounds](critical-worst-start-mixing-lower-bounds.md)
- [High-temperature SK heat-bath Poincaré and gap bounds](high-temperature-poincare-gap.md)

## Expansion

Establish a near-critical comparison between the variance-$\beta^2/n$ and variance-$1/n$ Gaussian disorder models, with enough slack to transfer both the discrete and continuous subexponential mixing upper bounds. Match the rate-one continuous clock, control disorder probability, and avoid substituting $\beta=1$ into the strictly high-temperature result. Combine with the linked critical lower bounds.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSKMixing.lean#L67-L75)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Critical slowing down in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf)
