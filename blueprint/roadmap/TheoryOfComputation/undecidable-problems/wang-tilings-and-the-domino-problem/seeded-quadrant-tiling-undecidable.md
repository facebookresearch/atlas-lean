# Seeded-quadrant Wang tiling is undecidable

It is undecidable whether a finite palette $T$ together with a seed tile $t_0\in T$ admits a tiling of the quadrant $\mathbb{N}^2$ with $t_0$ at the origin. Indeed, for every single-tape Turing machine $M$ there is a computable palette $T_M$ with seed such that the seeded quadrant tilings encode the successive configurations of $M$ on empty input row by row, so $T_M$ tiles the seeded quadrant iff $M$ never halts.

## Proof sketch

Row $k$ of the tiling spells the tape at time $k$: the colours on the top and bottom edges of a tile carry the tape symbol (and the state, at the head's cell) from row $k$ to row $k+1$, and the colours on the left and right edges pass the head between neighbouring cells when it moves; the seed tile and the bottom row start the computation on the empty tape, and no tile continues a halting state.

## Depends on

- [Seeded and every-tile-occurs variants of the tiling problem](wang-tiles.md)
- [Halting of a single-tape machine](../../computability/halting-problem-for-single-tape-turing-machines/tm0-halts-on.md)

## Sources

- Hao Wang, "Proving Theorems by Pattern Recognition II", Bell System Technical Journal 40(1), 1–41, 1961.
- Robert Berger, "The Undecidability of the Domino Problem", Memoirs of the American Mathematical Society 66, 1966.
- A. S. Kahr, E. F. Moore and H. Wang, "Entscheidungsproblem Reduced to the ∀∃∀ Case", Proceedings of the National Academy of Sciences 48(3), 365–377, 1962 (undecidability of the origin-constrained domino problem).
- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 177–209, 1971.
