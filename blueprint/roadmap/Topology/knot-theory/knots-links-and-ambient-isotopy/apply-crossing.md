# Tracing a strand through one crossing

Let a traversal state consist of a current
strand position $p \in \mathbb{N}$ and a list of vertices in $\mathbb{R}^3$, let
$w \in \mathbb{Z}$ be a braid generator with $i = |w|$, and let
$z_{\mathrm{top}}, z_{\mathrm{bot}} \in \mathbb{R}$. Put
$z_{\mathrm{hi}} = z_{\mathrm{top}} - (z_{\mathrm{top}} - z_{\mathrm{bot}})/4$ and
$z_{\mathrm{lo}} = z_{\mathrm{bot}} + (z_{\mathrm{top}} - z_{\mathrm{bot}})/4$. The new state is
obtained by changing the position and appending the listed points, in order, to the vertex
list. If $p = i$ and $w > 0$, the new position is $i + 1$ and the points are
$(i, 1, z_{\mathrm{hi}})$, $(i + 1, 1, z_{\mathrm{lo}})$, $(i + 1, 0, z_{\mathrm{bot}})$. If
$p = i$ and $w \le 0$, the new position is $i + 1$ and the only point is
$(i + 1, 0, z_{\mathrm{bot}})$. If $p = i + 1$ and $w > 0$, the new position is $i$ and the
only point is $(i, 0, z_{\mathrm{bot}})$. If $p = i + 1$ and $w \le 0$, the new position is
$i$ and the points are $(i + 1, 1, z_{\mathrm{hi}})$, $(i, 1, z_{\mathrm{lo}})$,
$(i, 0, z_{\mathrm{bot}})$. Otherwise the position stays $p$ and the only point is
$(p, 0, z_{\mathrm{bot}})$.

The step is meant for $z_{\mathrm{bot}} < z_{\mathrm{top}}$, with the crossing in the slab
between these heights: the strand passing over is lifted to $y = 1$, and the strand passing
under stays at $y = 0$.
