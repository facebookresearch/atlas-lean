# Whether polyominoes tile some rectangle is undecidable

No algorithm decides, given a finite set of polyominoes, whether translated copies of them tile some rectangle; this stays undecidable for sets of $19$ polyominoes.

Following the source, a *region* is a subset of $\mathbb Z^2$, viewed as a union of closed unit squares centered at its points; a *tile* (polyomino) is a finite region whose shape is simply connected, and a *tileset* $\mathcal T$ is a finite set of tiles. A $\mathcal T$-*tiling* of a region $\Gamma$ is a partition of $\Gamma$ into translated copies of tiles of $\mathcal T$ (no rotations or reflections), as in [translational tilings](translational-tilings-by-finitely-many-tiles.md).

**Theorem (Yang).** *Rectangular tileability* is undecidable: there is no algorithm that, given a tileset $\mathcal T$, decides whether some rectangle $[n\times m]$, $n,m\ge1$, is $\mathcal T$-tileable. The problem remains undecidable for tilesets of exactly $19$ polyominoes.

The rectangle is not part of the input: for a fixed rectangle the question is a finite search, and for a fixed tileset, tileability of a given $[n\times m]$ rectangle can be decided in time $O(\log n+\log m)$ (Lam, Miller and Pak, as recalled in the source).

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof works with generalized Wang tiles (polyominoes with colored edges) and then converts them into plain polyominoes by a geometric encoding that preserves tileability. From an instance of Post's correspondence problem it builds tiles whose rectangular tilings are bordered by special border tiles and whose interior rows spell the two concatenations, so that some rectangle is tileable iff the instance has a solution. Using the undecidability of the correspondence problem with $7$ pairs over a binary alphabet already bounds the number of tiles by $80$. For $19$, Ollinger's $11$ polyominoes simulating an arbitrary Wang tileset are combined with $8$ border tiles, so that the resulting set tiles some rectangle iff the Wang tileset tiles some suitably bordered rectangle.

## Sources

- Jed Yang, "Rectangular tileability and complementary tileability are undecidable", *European Journal of Combinatorics* 41, 2014, pp. 20–34, doi:[10.1016/j.ejc.2014.03.008](https://doi.org/10.1016/j.ejc.2014.03.008); read in arXiv:1212.3380v1 ([arXiv](https://arxiv.org/abs/1212.3380v1)), whose numbering is used: Theorem 1.2, Section 2 (definitions), Section 3 (Lemma 3.2 and Theorem 3.5, the bound of $19$ tiles) and the appendix on the geometric encoding of Wang tiles; Theorem 1.3 for the fixed-rectangle contrast.
