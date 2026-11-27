# Tiling the plane with translates of 7 polyominoes is undecidable

No algorithm decides, given a set of seven polyominoes, whether translated copies of them tile the plane; as a consequence there are aperiodic sets of seven polyominoes.

**Theorem.** The $7$-polyomino tiling problem is undecidable: there is no algorithm which, given a set of $7$ polyominoes, decides whether the plane can be tiled by translated copies of polyominoes from the set, in the sense of [translational tilings](translational-tilings-by-finitely-many-tiles.md) (translations only; no rotations or reflections).

The number of polyominoes is fixed at $7$ and their shapes are the input. A polyomino is a finite union of unit squares glued edge to edge. For one polyomino the problem is decidable, since a polyomino that tiles the plane by translations tiles it periodically. The source deduces (Corollary 1) that there are sets of $7$ polyominoes that tile the plane by translations but only non-periodically.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's domino problem: for each finite set of Wang tiles it builds $7$ polyominoes that tile the plane if and only if the Wang tiles do. The polyominoes are assembled from $10\times10$ functional squares carrying bumps and dents; pairs of building blocks encode the colors of Wang tile edges in binary, and the techniques of the authors' earlier three- and four-dimensional constructions are combined with new gadgets to reduce the eight polyominoes of the previous bound to seven. Since every set of polyominoes that tiles periodically could be found by enumeration, undecidability forces the existence of aperiodic sets of size $7$.

## Sources

- Chao Yang and Zhujun Zhang, "Translational aperiodic sets of 7 polyominoes", *Science China Mathematics*, 2026 (published online), doi:[10.1007/s11425-025-2593-4](https://doi.org/10.1007/s11425-025-2593-4); numbering of arXiv:2412.17382v1 ([arXiv](https://arxiv.org/abs/2412.17382v1)): Theorem 2 (undecidability with seven polyominoes), Corollary 1 (aperiodicity) and Section 2 (the proof).
