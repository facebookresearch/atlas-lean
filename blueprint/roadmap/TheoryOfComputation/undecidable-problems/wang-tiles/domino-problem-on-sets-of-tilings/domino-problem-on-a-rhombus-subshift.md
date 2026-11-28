# The domino problem on a rhombus subshift

Given a subshift $X$ of edge-to-edge tilings of the plane by finitely many rhombus shapes, the domino problem on $X$ asks whether a finite set of rhombus tiles with colored edges admits a tiling with matching colors whose underlying shape tiling lies in $X$.

**Geometrical tilings.** A *shape* is a rhombus given by two vectors $\vec u,\vec v$ and a position; a *shapeset* $\mathcal S$ is a finite set of shapes up to translation (not up to rotation). An *$\mathcal S$-tiling* is an edge-to-edge covering of $\mathbb R^2$ without overlap by translates of shapes of $\mathcal S$; the *full shift* $X_{\mathcal S}$ is the set of all $\mathcal S$-tilings, and a *rhombus subshift* is a subset $X\subseteq X_{\mathcal S}$ invariant under translation and closed in the tiling topology. Every subshift is the set of tilings avoiding some countable sequence $\mathcal F=(f_n)_n$ of forbidden finite patterns (patches up to translation); $X$ is *effective* when some such $\mathcal F$ is computable. Edge-to-edge rhombus tilings with finitely many shapes have finite local complexity, so these spaces are compact.

**Colored tiles.** For a finite set $C$ of colors, an *$r$-tile* is a shape $r$ together with a color from $C$ on each of its four edges, and an *$\mathcal S$-tileset* $\tau$ is a finite set of tiles on shapes of $\mathcal S$ containing at least one tile for each shape. A *$\tau$-tiling* is an edge-to-edge tiling by translates of tiles of $\tau$ in which tiles sharing an edge carry the same color on it; erasing colors, $\pi$, maps it to an $\mathcal S$-tiling.

**The problem.** For a fixed subshift $X$ on $\mathcal S$, $\mathrm{Domino}(X)$ asks, given an $\mathcal S$-tileset $\tau$, whether there is a $\tau$-tiling $x$ with $\pi(x)\in X$. The classical domino problem for Wang tiles is $\mathrm{Domino}(X_{\{\square\}})$, the full shift on a single shape.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles-and-valid-tilings.md)

## Proof depends on

None.

## Expansion

For the Penrose rhombuses, $\mathrm{Domino}(\mathrm{Penrose})$ asks for a tiling with matching edge colors that is a geometrical Penrose tiling once colors are erased. There is a tileset on the Penrose rhombuses whose valid tilings all project to Penrose tilings, even inside the full shift.

## Sources

- Benjamin Hellouin de Menibus, Victor H. Lutfalla and Camille Noûs, "The Domino Problem Is Undecidable on Every Rhombus Subshift", in *Developments in Language Theory (DLT 2023)*, Lecture Notes in Computer Science 13911, Springer, 2023, pp. 100–112, doi:[10.1007/978-3-031-33264-7_9](https://doi.org/10.1007/978-3-031-33264-7_9); numbering of arXiv:2302.12086v1 ([arXiv](https://arxiv.org/abs/2302.12086v1)): Section 2: the definitions of shapes, patches, tilings, full shifts and subshifts, effective subshifts, tiles and tilesets, the colour-erasing operator, tilings, and the problem $\mathrm{Domino}(X)$.
