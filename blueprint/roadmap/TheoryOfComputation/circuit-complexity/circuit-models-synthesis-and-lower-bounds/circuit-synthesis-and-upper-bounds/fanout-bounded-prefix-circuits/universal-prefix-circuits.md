# Universal prefix circuits and fanout-bounded optimality

A *prefix circuit* on $N$ inputs is a circuit over the basis $\{\ast,\mathrm{id}\}$ (a binary operation and an identity gate) which, interpreted in every semigroup $(S,\ast)$, outputs all prefix products $x_1,\ x_1\ast x_2,\ \dots,\ x_1\ast\cdots\ast x_N$ (equivalently, it does so in the free semigroup on $N$ generators). Its *complexity* $c$ is the number of $\ast$ gates and its *depth* $d$ counts both $\ast$ and $\mathrm{id}$ gates on a longest path. The *fanout* of a wire counts its gate inputs and output poles. A prefix circuit is *optimal* (has zero deficiency) if $c+d=2N-2$.

## Depends on

- [Straight-line programs and circuits over a basis](../../circuit-models-and-classes/circuit-models-and-complexity-measures/straight-line-program-over-a-basis.md)

## Sources

- Richard E. Ladner, Michael J. Fischer, "Parallel Prefix Computation", Journal of the ACM 27(4), 831–838, 1980.
- Marc Snir, "Depth-Size Trade-offs for Parallel Prefix Computation", Journal of Algorithms 7(2), 185–201, 1986.
- Igor S. Sergeev, "A Note on the Depth of Optimal Fanout-Bounded Prefix Circuits", arXiv:2512.23657, 2025 (preprint; terminology for fanout).
