# The domino problem is undecidable for Wang tile sets of color deficiency 25

No algorithm decides whether a given set of Wang tiles with color deficiency $25$ tiles the plane.

**Corollary.** The tiling problem restricted to finite sets $T$ of
[Wang tiles](wang-tiles-and-valid-tilings.md) with color deficiency $cd(T) = n(T) - c(T) = 25$, in the sense of
[Wang bars and the tiling problem for k Wang bars](wang-bars-and-the-tiling-problem-for-k-wang-bars.md), is undecidable.

Here $n(T)$ is the number of tiles and $c(T)$ the largest number of colors on one side, so the color deficiency is fixed while
the number of tiles and colors grows; fixing the number of tiles alone, or of colors alone, would leave only finitely many
instances. This improves the color deficiency $43$ of Jeandel and Rolin.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Wang bars and the tiling problem for k Wang bars](wang-bars-and-the-tiling-problem-for-k-wang-bars.md)

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

- C. Yang and Z. Zhang, "Undecidability of tiling the plane with a fixed number of Wang bars", *Journal of the Operations Research Society of China*, published online 2026, doi:10.1007/s40305-025-00666-0; Corollary 1 of the version arXiv:2404.04504v1 with its proof, and Theorem 3 (the transfer of Jeandel and Rolin).
