# Seeded-quadrant Wang tiling is undecidable

It is undecidable whether a finite palette $T$ together with a seed tile $t_0\in T$ admits a tiling of the quadrant $\mathbb{N}^2$ with $t_0$ at the origin. Indeed, for every single-tape Turing machine $M$ there is a computable palette $T_M$ with seed such that the seeded quadrant tilings encode the successive configurations of $M$ on empty input row by row, so $T_M$ tiles the seeded quadrant iff $M$ never halts.

## Proof sketch

Row $k$ of the tiling spells the tape at time $k$; colours on vertical edges carry tape symbols, and the head with its state is propagated by horizontal colour constraints; the seed row starts the computation, and no tile exists for a halting state.

## Depends on

- [Seeded and every-tile-occurs variants of the tiling problem](wang-tiles.md)
- [Halting of a single-tape machine](../../computability/halting-problem-for-single-tape-turing-machines/tm0-halts-on.md)

## Sources

- Hao Wang, "Proving Theorems by Pattern Recognition II", Bell System Technical Journal 40, 1961.
- Robert Berger, "The Undecidability of the Domino Problem", Memoirs of the American Mathematical Society, 1966.
- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 1971.
