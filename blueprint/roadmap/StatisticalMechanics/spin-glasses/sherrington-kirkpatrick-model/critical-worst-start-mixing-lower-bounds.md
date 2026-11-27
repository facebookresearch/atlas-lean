# Critical SK worst-start mixing lower bounds

In the [critical Gibbs heat bath](gaussian-sk-heat-bath.md), define $t_c$ as the infimum of nonnegative real times at which all starting states have total-variation distance at most $1/4$, and $t_d$ as the first natural update count with that property. For each fixed $\varepsilon>0$, the disorder probability of $t_c\ge n^{2/3-\varepsilon}$ tends to one, and the disorder probability of $t_d\ge n^{5/3-\varepsilon}$ tends to one, with $t_d$ cast to a real for the comparison. The count is of attempted single-site updates, not accepted changes of spin.

**Conventions.** Use the [site heat-bath kernels, clock normalization and distance](gaussian-sk-heat-bath.md) and their worst-start mixing functionals.

The real and natural cutoff infima use their native value zero on the empty set.

## Depends on

- [Gaussian SK energy and the single-site heat bath](gaussian-sk-heat-bath.md)

## Proof depends on

- [Critical typical-start obstruction](critical-realized-equilibrium-starts.md)

## Proof outline

Use monotonicity of worst-start distance under both Markov evolutions.

Choose test times below the two critical scales, with the required real or natural rounding, and pass from positive Gibbs mass of bad starts to a worst-start lower bound. Treat the small-size time-zero convention separately from the limit.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSK.lean#L136-L144)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/227.md)
- [Accompanying manuscript: Critical slowing down in the Sherrington–Kirkpatrick model](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf)
