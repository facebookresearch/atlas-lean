# Tiling 4-space with translates of 4 polyhypercubes is undecidable

No algorithm decides, given a set of four polyhypercubes, whether translated copies of them tile four-dimensional space.

A *polyhypercube* is a connected union of finitely many unit hypercubes of the integer lattice in $\mathbb R^4$ glued face to face; it is a finite tile in $\mathbb Z^4$ in the sense of [translational tilings](translational-tilings-by-finitely-many-tiles.md), with $G=E=\mathbb Z^4$.

**Theorem.** There is no algorithm which, given a set of $4$ polyhypercubes, decides whether $\mathbb R^4$ (equivalently $\mathbb Z^4$) can be tiled by translated copies of polyhypercubes from the set (translations only).

The number of tiles $k=4$ and the dimension $n=4$ are fixed; the shapes are the input. In dimension one, and for a single tile in dimension two, translational tiling is decidable; the source presents the result as a step towards undecidability with one tile in some fixed dimension.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Tiling 3-space with translates of 5 polycubes is undecidable](tiling-z3-with-5-polycubes-is-undecidable.md)

## Expansion

The five-polycube tile set of the three-dimensional proof, and its tilings, are lifted to four dimensions: the lifting technique merges two of the tiles at the cost of one more dimension, using $8\times8\times8\times8$ functional hypercubes and their halves, so that the resulting $4$ polyhypercubes tile $\mathbb Z^4$ iff the original Wang tile set tiles the plane.

A good expansion links a page for the lifting technique and the lemma that the lifted tile set tiles $\mathbb Z^4$ exactly when the five polycubes tile $\mathbb Z^3$.

## Sources

- Chao Yang and Zhujun Zhang, "Undecidability of translational tiling of the 4-dimensional space with a set of 4 polyhypercubes", *Science China Mathematics* 68(9), 2025, pp. 2173–2188, doi:[10.1007/s11425-024-2365-2](https://doi.org/10.1007/s11425-024-2365-2); numbering of arXiv:2409.00846v2 ([arXiv](https://arxiv.org/abs/2409.00846v2)): Theorem 3 (undecidability with four tiles) and Section 3 (its proof by lifting); the decidable cases recalled in Section 1.
