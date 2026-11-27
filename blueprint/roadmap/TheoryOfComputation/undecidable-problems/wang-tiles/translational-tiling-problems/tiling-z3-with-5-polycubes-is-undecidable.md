# Tiling 3-space with translates of 5 polycubes is undecidable

No algorithm decides, given a set of five polycubes, whether translated copies of them tile three-dimensional space.

A *polycube* is a finite union of unit cubes of the integer lattice in $\mathbb R^3$ glued face to face; equivalently, a finite tile in $\mathbb Z^3$ in the sense of [translational tilings](translational-tilings-by-finitely-many-tiles.md), with $G=E=\mathbb Z^3$.

**Theorem.** There is no algorithm which, given a set of $5$ polycubes, decides whether $\mathbb R^3$ (equivalently $\mathbb Z^3$) can be tiled by translated copies of polycubes from the set (translations only).

The number of tiles is fixed at $5$; their shapes are the input. This improves the earlier bound of $6$ polycubes due to the same authors.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's domino problem directly in dimension three, without lifting a planar construction. Tiles are assembled from $8\times8\times8$ functional cubes with bumps and dents that encode Wang tile colors; the construction is designed to be compatible with the lifting technique, which trades one tile for one extra dimension and is used afterwards for the four-dimensional result.

## Sources

- Chao Yang and Zhujun Zhang, "Undecidability of translational tiling of the 4-dimensional space with a set of 4 polyhypercubes", *Science China Mathematics* 68(9), 2025, pp. 2173–2188, doi:[10.1007/s11425-024-2365-2](https://doi.org/10.1007/s11425-024-2365-2); numbering of arXiv:2409.00846v2 ([arXiv](https://arxiv.org/abs/2409.00846v2)): Theorem 4 (undecidability with five tiles) and Section 2 (its proof); Theorem 2 (six polycubes, the earlier bound).
