# A common continuum free-energy corner for a divergent-core potential

There exist a radial potential $\phi:\mathbb R\to\mathbb R$, a finite real function $f(\beta,\rho)$, a nonempty open interval $I\subset(0,\infty)$, and $\beta_c\in(1/2,3/2)$ with the following properties. The interaction at displacement $x$ is $\phi(|x|)$ for $x\ne0$ and $+\infty$ at collision, and this extended-real interaction is measurable. The potential is bounded above and below on each compact interval of positive radii, tends to $+\infty$ as $r\downarrow0$, and is bounded above by a negative constant on some closed interval $[r_1,r_2]$ with $0<r_1<r_2$. Its tail satisfies $\int_R^\infty r^2|\phi(r)|\,dr<\infty$ for some $R>0$, and $\phi(r)=o(r^{-3})$ as $r\to\infty$. For some $B$ its total pair energy is at least $-BN$ for every $N$-particle configuration.

Let $Z=1$ for zero particles and otherwise $N!^{-1}\int e^{-\beta E_N}$ over the product of centered cubes $[-L/2,L/2]^3$, with Boltzmann weight zero at configurations of energy $+\infty$. For every $\beta,\rho>0$, as $L\to\infty$ with $N=\lfloor\rho L^3\rfloor$, $L^{-3}\log Z\to-\beta f(\beta,\rho)$. For every $\rho\in I$ there are finite left and right derivatives of $f(\cdot,\rho)$ at the same $\beta_c$, with the right derivative strictly smaller.

**Conventions.** Use extended-real stable pair energy and the canonical partition integral, with divergent core, zero collision weight, and factorial and inverse-temperature normalization as stated.

## Depends on

- [Canonical radial Gibbs weight in a finite box](canonical-radial-weight.md)

## Proof depends on

A stable potential construction with a repulsive core and attractive well, a canonical thermodynamic limit for all positive densities and temperatures, and control of competing canonical branches on a common open density interval.

## Expansion

Separate admissibility of the interaction from the partition limit. Derive the strict inequality for the one-sided derivatives of $f$, rather than for an unconverted log-partition quantity. The bounded continuous potential with algebraic tail is a different construction.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContinuumTransition.lean#L59-L61)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/228.md)
- [Accompanying manuscript: A continuum temperature singularity for a radial pair potential](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-continuum-temperature-singularity-for-a-radial-pair-potential-September-24-2026/paper.pdf)
