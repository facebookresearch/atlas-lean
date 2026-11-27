# The tiling problem for 29 Wang bars is undecidable

No algorithm decides whether a given set of $29$ Wang bars tiles the plane.

**Theorem.** The [tiling problem for $k$ Wang bars](wang-bars-and-the-tiling-problem-for-k-wang-bars.md) is undecidable for
$k = 29$.

The number of bars is fixed at $29$; the lengths of the bars and their colors vary. This improves the bound of $44$ Wang bars
of Jeandel and Rolin, who also claimed without proof that $35$ suffice.

## Depends on

- [Wang bars and the tiling problem for k Wang bars](wang-bars-and-the-tiling-problem-for-k-wang-bars.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

The proof follows Ollinger's method for tiling with a fixed number of polyominoes. Given an arbitrary finite set of Wang tiles,
it builds $29$ Wang bars whose lengths and colors encode the tiles: *encoders* write the colors of a tile on their arms,
*selectors* choose a tile, *linkers* join the arms that encode the same color of adjacent tiles, *aligners* fill horizontal gaps
and *fillers* fill the remaining area. A sequence of forcing facts shows that every tiling by the $29$ bars has this backbone,
so the bars tile the plane if and only if the given Wang tile set does. Undecidability of the tiling problem for Wang tiles
(Berger) then transfers.

## Sources

- C. Yang and Z. Zhang, "Undecidability of tiling the plane with a fixed number of Wang bars", *Journal of the Operations Research Society of China*, published online 2026, doi:10.1007/s40305-025-00666-0; Theorem 4 of the version arXiv:2404.04504v1 with its proof in Section 2, and Theorem 2 (the bound of Jeandel and Rolin).
