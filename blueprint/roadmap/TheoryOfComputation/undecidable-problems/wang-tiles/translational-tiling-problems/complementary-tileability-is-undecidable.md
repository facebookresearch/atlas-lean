# Tiling the complement of a finite region is undecidable

There is a fixed finite set of polyominoes for which no algorithm decides whether the complement of a given finite region of the plane can be tiled; and for every fixed finite simply connected region, no algorithm decides whether a given set of polyominoes tiles its complement.

Following the source, a *region* is a subset of $\mathbb Z^2$, viewed as a union of closed unit squares centered at its points; a *tile* (polyomino) is a finite region whose shape is simply connected, and a *tileset* $\mathcal T$ is a finite set of tiles. A $\mathcal T$-*tiling* of a region $\Gamma$ is a partition of $\Gamma$ into translated copies of tiles of $\mathcal T$ (no rotations or reflections), as in [translational tilings](translational-tilings-by-finitely-many-tiles.md).

**Theorem (Yang).**
1. There is a tileset $\mathcal T$ such that it is undecidable, given a finite region $\Gamma\subseteq\mathbb Z^2$, whether $\mathbb Z^2\setminus\Gamma$ is $\mathcal T$-tileable (Theorem 4.1).
2. For every finite simply connected region $\Gamma$, it is undecidable, given a tileset $\mathcal T$, whether $\mathbb Z^2\setminus\Gamma$ is $\mathcal T$-tileable (Theorem 4.2); in particular already when $\Gamma$ is a single unit square.

Simple connectivity in item 2 is needed: if $\Gamma$ has a hole of one unit square, its complement is tileable exactly when $\mathcal T$ contains a single unit square. By contrast, the source gives an algorithm deciding whether the complement of a finite region is tileable by a given set of rectangles.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem is undecidable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

For item 1, fix a universal Turing machine. A finite region $\Gamma_x$ encodes an input word $x$ and the start state along a boundary, and a fixed set of Wang tiles emulating the machine must fill the cofinite complement: the emulation can be completed to the whole complement iff the machine does not halt on $x$ (a halting configuration cannot be continued), and the Wang tiles are then converted to polyominoes. Item 2 reduces item 1 to a fixed region: given $\mathcal T$ and $\Gamma$, pass $\mathcal T \cup \{\Gamma\}$ to Wang tiles and back to polyominoes, scale all tiles by $2$ and remove one unit square from the tile corresponding to $\Gamma$; the new tiles align in a dilated grid in every tiling, so $\mathbb Z^2$ minus a unit square is tileable by them iff $\mathbb Z^2\setminus\Gamma$ is $\mathcal T$-tileable, and other fixed simply connected regions are handled the same way. The source notes that this is essentially the origin-constrained tiling problem (Wang).

## Sources

- Jed Yang, "Rectangular tileability and complementary tileability are undecidable", *European Journal of Combinatorics* 41, 2014, pp. 20–34, doi:[10.1016/j.ejc.2014.03.008](https://doi.org/10.1016/j.ejc.2014.03.008); read in arXiv:1212.3380v1 ([arXiv](https://arxiv.org/abs/1212.3380v1)), whose numbering is used: Section 4: Theorems 4.1 and 4.2 and their proofs, and the subsection on tiling cofinite regions with rectangles; Theorem 1.1.
