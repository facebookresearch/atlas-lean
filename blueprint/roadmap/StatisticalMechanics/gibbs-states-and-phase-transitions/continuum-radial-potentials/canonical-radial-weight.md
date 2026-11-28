# Canonical radial Gibbs weight in a finite box

On a bounded Euclidean box, use Lebesgue measure on ordered $n$-tuples. The energy is the sum over unordered distinct particle labels of the radial pair potential applied to their distance. With inverse temperature $\beta>0$, the configurational partition integral is $1/n!$ times the integral of $e^{-\beta E}$, with weight zero at infinite positive energy. No momentum degrees of freedom are included. A hard-core potential can therefore impose a separation constraint directly through its infinite energy. For fixed density the particle count in growing boxes is the natural floor of density times volume; the resulting limiting functions retain the particular volume or particle normalization of the stated endpoint.

In the bounded-potential variant the radial function has domain the nonnegative reals and is finite even at zero. The box is $[0,L]^3$, the energy sums unordered pairs with this finite value, and the partition function is the integral of the exponential divided by $N!$. The thermodynamic limit for fixed density uses the corresponding particle counts and normalization stated by the endpoint. Do not apply the divergent-core collision convention to this variant.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContinuumTransition.lean#L10-L45)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RadialDensityInterval.lean#L12-L55)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RadialTransition.lean#L12-L55)
