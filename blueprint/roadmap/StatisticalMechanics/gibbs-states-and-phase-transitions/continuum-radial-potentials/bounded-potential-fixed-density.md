# A bounded radial potential with a free-energy corner at fixed density

Use the [packing and bounded-potential canonical model](bounded-potential-density-interval.md). There are $p>0$ with $M(L)/L^3\to p$, a bounded continuous $\phi$ with stability bound $E_N\ge-BN$ and tail bound $|\phi(r)|\le C r^{-3-1/32}$ ($B,C>0$, $r\ge1$), a real function $f$, and $\beta_c\in[7/8,9/8]$. At the single density $\rho=5p/3$, the limit $-\log Z(L,\lfloor\rho L^3\rfloor,\beta)/(\beta L^3)\to f(\beta)$ holds for every $\beta>0$. At $\beta_c$ the strict inequality between finite one-sided derivatives is $f'_+(\beta_c)<f'_-(\beta_c)$ and the ordinary derivative does not exist.

## Depends on

- [Canonical radial Gibbs weight in a finite box](canonical-radial-weight.md)
- [Bounded-potential transition on a density interval](bounded-potential-density-interval.md)

## Proof depends on

- [The common-corner density interval result](bounded-potential-density-interval.md)

## Proof outline

Specialize the interval result at its center (or use the fixed-density branch construction directly). The fixed-density claim does not itself establish an interval of densities.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RadialTransition.lean#L57-L65)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/228.md)
- [Accompanying manuscript: A radial continuum phase transition with algebraic decay](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf)
