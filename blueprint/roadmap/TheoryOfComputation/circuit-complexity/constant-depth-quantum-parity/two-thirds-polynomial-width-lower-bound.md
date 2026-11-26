# A two-thirds parity lower bound at polynomial total qubit count

For natural $d,k,C>0$, use the [same quantum gate, scheduling and output model](general-advantage-parity-lower-bound.md). There is $n_0$ such that for all $n\ge n_0$ and $n\le N\le C(n+1)^k$, every circuit of depth at most $d$ and every chosen output index has an $n$-bit input with success probability strictly below $2/3$.

## Depends on

- [Disjoint-support quantum layers with unbounded controls](unbounded-control-quantum-circuits.md)
- [The allowed circuits and success probability](general-advantage-parity-lower-bound.md)

## Proof depends on

- [The general-advantage parity lower bound](general-advantage-parity-lower-bound.md)

## Expansion

Choose $\varepsilon=1/6$ and a real exponent eventually absorbing the fixed factor and the shift in $C(n+1)^k$. Retain the asserted bound for all allowed widths and chosen output indices, with the counterinput permitted to depend on both the circuit and the index.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/RegularParity.lean#L61-L70)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/274.md)
- [Accompanying manuscript: Regular trajectories, pruning and quantum parity](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Regular-trajectories-pruning-and-quantum-parity-September-24-2026/paper.pdf)
