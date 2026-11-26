# A common free-energy corner for a bounded radial potential on a density interval

Let $M(L)$ be the largest number of points in $[0,L]^3$ with pairwise distances at least $1$. There exist a positive packing-density limit $p=\lim_{L\to\infty}M(L)/L^3$, one bounded continuous radial pair potential $\phi:[0,\infty)\to\mathbb R$, and constants $B,C>0$ so that $E_N(x)=\sum_{i<j}\phi(|x_i-x_j|)\ge-BN$ for every configuration and $|\phi(r)|\le C r^{-3-1/32}$ for $r\ge1$.

For $N=\lfloor\rho L^3\rfloor$, let $Z(L,N,\beta)=N!^{-1}\int_{([0,L]^3)^N}e^{-\beta E_N(x)}\,dx$. There are $\eta>0$ with $I=(5p/3-\eta,5p/3+\eta)\subset(0,\infty)$ and one $\beta_c\in[7/8,9/8]$ such that the limit of $-\log Z/(\beta L^3)$ exists as a finite real $f(\beta,\rho)$ for every $\rho\in I$ and $\beta>0$. At every $\rho\in I$ the left and right derivatives in $\beta$ at $\beta_c$ exist as finite reals, the right derivative is strictly less than the left derivative, and $f(\cdot,\rho)$ is not differentiable there.

**Conventions.** Use the unit-separated packing limit and canonical configurational integral with natural floor for the particle count, no momentum factor, and a factorial correction.

## Depends on

- [Canonical radial Gibbs weight in a finite box](canonical-radial-weight.md)

## Proof depends on

A bounded stable radial interaction construction, thermodynamic-limit control on a density interval, and two phases whose canonical branch comparison yields a common strict transverse corner.

## Expansion

Prove existence and positivity of the packing limit and uniform-in-density estimates on an explicit neighborhood of $5p/3$. Separate the free-energy limit from the quantitative slope bounds on both sides of the same critical inverse temperature.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RadialDensityInterval.lean#L57-L68)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/228.md)
- [Accompanying manuscript: A radial continuum phase transition with algebraic decay](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf)
