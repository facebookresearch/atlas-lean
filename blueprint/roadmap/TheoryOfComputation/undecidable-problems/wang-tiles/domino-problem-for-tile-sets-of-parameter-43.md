# The domino problem is undecidable for Wang tile sets of parameter 43

Let $n$ be the number of tiles of a Wang tile set and $c$ the largest number of colors on one of its four sides. Whether a tile set tiles the plane is undecidable already for the tile sets with $n - c = 43$, and for those with $n - c = k$ for each fixed $k \ge 43$.

Let $\tau$ be a finite set of [Wang tiles](wang-tiles-and-valid-tilings.md). Write $n(\tau)$ for the number of tiles of $\tau$ and $c(\tau)$ for the maximum, over the four sides (north, east, south, west), of the number of distinct colors that the tiles of $\tau$ carry on that side; thus $c(\tau) \le n(\tau)$, and $n(\tau) - c(\tau) \ge 0$ is the *parameter* of $\tau$. The *domino problem* asks, given $\tau$, whether $\tau$ admits a valid tiling of $\mathbb{Z}^2$ (tiles are translated, never rotated or reflected).

**Theorem.** For every fixed integer $k \ge 43$, the domino problem restricted to tile sets $\tau$ with $n(\tau) - c(\tau) = k$ is undecidable: no algorithm decides, given such a $\tau$, whether it admits a valid tiling.

Fixing $n(\tau)$ alone, or $c(\tau)$ alone, leaves only finitely many tile sets up to renaming colors, so those restrictions are trivially decidable; the parameter $n - c$ is the quantity for which a threshold appears. At the other end, a tile set of parameter at most $1$ admits a tiling if and only if it admits a periodic tiling, so the domino problem is decidable for parameter $n - c \le 1$ (Jeandel and Rolin, Theorem 1.1), and the Kari–Culik tile set is an aperiodic tile set of parameter $8$. What happens for parameters $2$ to $42$ is left open by the source.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

A *Wang bar* is a tile that is longer horizontally: a quadruple $(b_e, b_w, b_n, b_s)$ whose north and south labels are words of equal length over the color set. Viewing a tile set as a labeled multigraph on the west/east colors (tiles are edges, rows of a tiling are bi-infinite paths), tileability by a tile set of parameter $k$ is related to tileability by $O(k)$ Wang bars (Section 2 of the source). Section 3 then reduces the general domino problem to tileability by a fixed number of bars: from an arbitrary Wang tile set it builds a set of $44$ Wang bars that tiles the plane if and only if the tile set does, so tileability by $44$ bars is undecidable (Theorem 3.1), and Theorem 2.1, which turns $k$ bars into a tile set of parameter at most $k - 1$, then gives undecidability for tile sets of parameter exactly $43$ (Corollary 3.1). The source states that undecidability persists for every larger parameter. A good expansion links pages for the conversion of Wang bars into tile sets of bounded parameter (Theorem 2.1 of the source) and for the construction of the $44$ bars (Theorem 3.1).

## Sources

- E. Jeandel and N. Rolin, "Fixed Parameter Undecidability for Wang Tilesets", in E. Formenti (ed.), *Proceedings AUTOMATA and JAC 2012*, Electronic Proceedings in Theoretical Computer Science 90, 2012, pp. 69–85, doi:[10.4204/EPTCS.90.6](https://doi.org/10.4204/EPTCS.90.6); numbering of arXiv:1208.2769v1: the definition of the parameter in Section 1, Theorem 1.1 (parameter at most 1), Theorem 1.2 (parameter 43 and higher), Theorem 3.1 (44 Wang bars) and Corollary 3.1.
