# Augmentability of a region by polyominoes is undecidable

No algorithm decides, given polyominoes and a finite region, whether the region can be enlarged to a finite simply connected region that is tileable and whose added part is tileable too; this holds already with the region fixed, or with the tileset fixed.

Following the source, a *region* is a subset of $\mathbb Z^2$, viewed as a union of closed unit squares centered at its points; a *tile* (polyomino) is a finite region whose shape is simply connected, and a *tileset* $\mathcal T$ is a finite set of tiles. A $\mathcal T$-*tiling* of a region $\Gamma$ is a partition of $\Gamma$ into translated copies of tiles of $\mathcal T$ (no rotations or reflections), as in [translational tilings](translational-tilings-by-finitely-many-tiles.md).

A finite region $\Gamma$ is *augmentable* by $\mathcal T$ if there is a finite simply connected region $\Gamma'\supseteq\Gamma$ such that both $\Gamma'\setminus\Gamma$ and $\Gamma'$ are $\mathcal T$-tileable. The empty region counts as tiled by the empty tiling; the source writes $\Gamma'\supset\Gamma$, and with $\Gamma'=\Gamma$ allowed a simply connected $\mathcal T$-tileable $\Gamma$ is augmentable trivially. The regions $\Gamma_x$ of the reduction below are not tileable, so the theorem holds under either reading. An instance is $\mathcal T$ and $\Gamma$ given as finite lists of cells of $\mathbb Z^2$.

**Theorem (Yang).** It is undecidable, given a tileset $\mathcal T$ and a finite region $\Gamma$, whether $\Gamma$ is augmentable by $\mathcal T$. It remains undecidable when $\Gamma$ is fixed, and there is a tileset $\mathcal T$ for which it is undecidable with $\mathcal T$ fixed.

For dominoes, an augmentable region must be balanced (equally many black and white squares in the checkerboard coloring), but balance is not sufficient (Korn).

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem is undecidable by multi-stack machines](../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)

## Expansion

The reduction is from halting of a Turing machine $M$ with a one-way infinite tape, the head starting at the left end of the input. The tileset consists of Wang tiles emulating the computation of $M$ (machine tiles), border tiles, and filler tiles; boundary colors are chosen so that border tiles can only sit on the boundary and filler tiles only next to filler tiles. A finite region $\Gamma_x$ carries the input $x$ and the start state on its lower boundary. If $M$ halts on $x$, the space-time diagram of the halting computation placed under $\Gamma_x$ and surrounded by border tiles, with a halting tile on the bottom row, tiles $\Gamma'\setminus\Gamma_x$ for a rectangle $\Gamma'$, and $\Gamma'$ itself is tiled by filler tiles. Conversely, in any augmentation $\Gamma'$ must be a rectangle tiled by filler tiles alone, and $\Gamma'\setminus\Gamma_x$ is tiled by border and machine tiles with exactly one halting tile, which encodes a halting computation on $x$. Exchanging the roles of $\Gamma_x$ and one filler tile fixes the region; fixing $M$ universal fixes the tileset. Wang tiles are finally converted into polyominoes.

## Sources

- Jed Yang, "Rectangular tileability and complementary tileability are undecidable", *European Journal of Combinatorics* 41, 2014, pp. 20–34, doi:[10.1016/j.ejc.2014.03.008](https://doi.org/10.1016/j.ejc.2014.03.008); read in arXiv:1212.3380v1 ([arXiv](https://arxiv.org/abs/1212.3380v1)), whose numbering is used: Section 6, Theorem 6.1 and its proof.
