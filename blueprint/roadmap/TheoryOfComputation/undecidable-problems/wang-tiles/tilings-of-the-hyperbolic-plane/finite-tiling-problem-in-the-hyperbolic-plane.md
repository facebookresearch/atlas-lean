# The finite tiling problem is undecidable in the hyperbolic plane

No algorithm decides whether a finite set of heptagonal tiles of the hyperbolic tessellation {7,3}, together with a blank tile, admits a tiling of the hyperbolic plane that uses only finitely many non-blank tiles but at least one.

**Setting.** The *heptagrid* is the tiling $\{7,3\}$ of the hyperbolic plane by copies of the regular heptagon with interior angles $2\pi/3$, obtained from one heptagon by repeated reflection in its edges. A tile is a copy of this heptagon placed on a cell of the heptagrid, with a color on each side, and a tiling of the hyperbolic plane by copies of a finite set of tiles is *valid* if any two tiles sharing a side carry the same color on it, as for [Wang tiles](../wang-tiles-and-valid-tilings.md) in the Euclidean plane. An instance lists finitely many prototiles, each by the colors of its seven sides. A copy of a prototile is its image under an orientation-preserving isometry of the heptagrid: rotations are allowed and reflections are not, the convention of the harp construction that the proof modifies (Section 1 of the paper on the harp cited below). This differs from the isocline-preserving convention of [the general domino problem of the hyperbolic plane](the-domino-problem-of-the-hyperbolic-plane-is-un.md). The *finite tiling problem* asks, given a finite set $T$ of tiles and a tile $b\notin T$, the *blank*, whether there is a valid tiling of the plane with copies of $T\cup\{b\}$ in which there are only finitely many copies of tiles of $T$ but at least one.

**Theorem (Margenstern).** The finite tiling problem is undecidable in the hyperbolic plane (Theorem 1).

In the Euclidean plane the finite tiling problem is undecidable as well ([the finite tiling problem](../the-finite-tiling-problem-is-undecidable.md)), a result of Kari that he used to prove the undecidability of surjectivity for two-dimensional cellular automata. The source discusses obstacles to transferring that application to the hyperbolic plane.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape Turing machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof modifies Margenstern's solution of the origin-constrained problem in the heptagrid, the *harp*: inside an angular sector spanned by a Fibonacci tree of the tiling, the tiles simulate the space-time diagram of a Turing machine on a semi-infinite tape started on the empty tape. The borders of the sector receive a special silver signal, which is also emitted along the current level when the machine halts; the two signals meet in corner tiles, closing off a finite region outside which all edges are blank. So the machine halts exactly when a finite nontrivial tiling exists: a halting computation yields one, and conversely, since tiles of $T$ off the border have no blank edge, a finite nonblank region must be closed by left, right and level borders, which forces the origin of the harp and a halting simulation inside it. A good expansion links a page for the heptagrid (its cells, side adjacency and orientation-preserving isometries) with heptagonal tiles colored on their sides and their valid tilings, and a page for the harp, Margenstern's tiling of the heptagrid that simulates Turing machines from an origin.

## Sources

- Maurice Margenstern, "The finite tiling problem is undecidable in the hyperbolic plane", *International Journal of Foundations of Computer Science* 19(4), pp. 971–982, 2008, doi:[10.1142/S0129054108006078](https://doi.org/10.1142/S0129054108006078); read in arXiv:cs/0703147v1 ([arXiv](https://arxiv.org/abs/cs/0703147v1)), whose numbering is used: the statement of the finite tiling problem in Section 1, Theorem 1, the description of the tiling $\{7,3\}$ and of the harp in Section 2, the proof in Section 3, and the conclusion in Section 4.
- Maurice Margenstern, "About the domino problem in the hyperbolic plane from an algorithmic point of view", *RAIRO – Theoretical Informatics and Applications* 42(1), pp. 21–36, 2008, doi:[10.1051/ita:2007045](https://doi.org/10.1051/ita:2007045); read in arXiv:cs/0603093v1 ([arXiv](https://arxiv.org/abs/cs/0603093v1)), reference [8] of the source above: Section 1 (only reflections are ruled out; rotations of the tiles are allowed).
