# Gaussian SK energy and the single-site heat bath

For $n$ Ising spins $s_i\in\{-1,1\}$ and symmetric Gaussian couplings with one independent variance-$1/n$ draw per unordered pair of distinct sites, use the zero-field energy sum $\sum_{i<j}J_{ij}s_i s_j$. At inverse temperature $\beta$, the stationary Gibbs law gives a configuration mass proportional to the exponential of $\beta$ times this sum. An update at site $i$ retains the other spins and chooses $a\in\{-1,1\}$ with probability $\exp(\beta a h_i)/(2\cosh(\beta h_i))$, where $h_i=\sum_{j\ne i}J_{ij}s_j$. The discrete kernel averages the $n$ single-site kernels uniformly. Its continuous rate-one-per-site generator is the sum of the individual update operators minus identity at each site, not the single averaged generator. Total variation is half the sum of absolute differences. The worst-start mixing time uses the maximal distance to this Gibbs law from a single configuration, at the prescribed tolerance; it differs from a mixing time for a specified initial law.

At criticality take $\beta=1$. Equivalently one can use standard Gaussian couplings and divide their sum by $\sqrt n$ before applying $\beta$, or absorb $\beta$ into the couplings using variance $\beta^2/n$ and use the exponential of the resulting energy. The discrete spectral gap uses the Rayleigh quotient with the averaged single-site conditional variances, whereas the rate-one-per-site form uses their sum. The continuous worst-start mixing time is the real infimum over nonnegative times satisfying the distance cutoff; the discrete version is the natural infimum over step counts. At an empty constraint use the infimum convention of the respective ordered type.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSK.lean#L20-L74)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CriticalSKMixing.lean#L11-L65)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKHighTemperature.lean#L11-L62)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKBarriers.lean#L14-L71)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SKRatio.lean#L11-L57)
