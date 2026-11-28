# The domino problem is undecidable for Wang tile sets of color deficiency 25

No algorithm decides whether a given set of Wang tiles with color deficiency $25$ tiles the plane.

For a finite set $T$ of [Wang tiles](wang-tiles-and-valid-tilings.md), let $n(T) = |T|$ and let $c(T)$ be the maximum, over the four
sides, of the number of different colors that the tiles of $T$ carry on that side; the *color deficiency* of $T$ is
$cd(T) = n(T) - c(T) \ge 0$ (Definition 2 of the source).

**Corollary.** The tiling problem restricted to finite sets $T$ of Wang tiles with color deficiency $cd(T) = 25$ is undecidable
(Corollary 1 of the source).

The color deficiency is fixed while
the number of tiles and colors grows; fixing the number of tiles alone, or of colors alone, would leave only finitely many
instances. This improves the color deficiency $43$ of Jeandel and Rolin (Theorem 1.2 of their paper).

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem for 29 Wang bars is undecidable](the-tiling-problem-for-29-wang-bars-is-undecidab.md)

## Expansion

The proof follows Jeandel and Rolin's transfer from Wang bars to Wang tiles. Take the $29$ Wang bars of the reduction for the
$29$-bar theorem and cut every bar of length $\ell \ge 2$ into pieces of length $1$ and $\ell - 1$, giving the two new vertical
sides a fresh common color, until only Wang tiles remain. After $t$ cuts there are $29 + t$ tiles, and the east and west sides
carry the $4$ colors of the bars plus the $t$ new ones, so $c(T) \ge 4 + t$ and $cd(T) \le 25$. Adding tiles that take part in
no tiling raises the color deficiency to exactly $25$ without changing which sets tile the plane. The resulting tile set tiles
the plane exactly when the bars do.

## Sources

- C. Yang and Z. Zhang, "Undecidability of tiling the plane with a fixed number of Wang bars", *Journal of the Operations Research Society of China*, published online 2026, doi:10.1007/s40305-025-00666-0; Definition 2 and Corollary 1 of the version arXiv:2404.04504v1 with its proof, and Theorem 3 (the transfer of Jeandel and Rolin).
- E. Jeandel and N. Rolin, "Fixed parameter undecidability for Wang tilesets", in *Proceedings of AUTOMATA 2012 and JAC 2012*, Electronic Proceedings in Theoretical Computer Science 90, pp. 69–85, 2012, doi:10.4204/EPTCS.90.6; read in arXiv:1208.2769v1: Theorem 1.2 (the domino problem for tilesets of parameter $n - c = 43$ is undecidable).
