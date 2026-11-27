# Wang tiles and valid tilings

A *Wang tile* $t$ is a unit square with colored edges, with colors $t_N, t_E, t_S, t_W$ on its north, east, south and west
edges, taken from some set of colors. A *tile set* $T$ is a finite set of Wang tiles. A *tiling* with $T$ is a map
$t : \mathbb{Z}^2 \to T$, placing copies of tiles at the integer lattice points without rotating or reflecting them. It is
*valid at* $(x, y)$ when the tile there matches its four neighbors:
$t(x, y)_N = t(x, y + 1)_S$, $t(x, y)_S = t(x, y - 1)_N$, $t(x, y)_E = t(x + 1, y)_W$ and $t(x, y)_W = t(x - 1, y)_E$,
and *valid* when it is valid at every point. A tiling is *periodic* if it is invariant under two non-parallel translations
of $\mathbb{Z}^2$, and a tile set is *aperiodic* if it admits a valid tiling but no valid periodic tiling. A tile set is
*NW-deterministic* if any two tiles $s, t \in T$ with $s_N = t_N$ and $s_W = t_W$ are equal.

By compactness, a tile set that admits valid tilings of arbitrarily large squares admits a valid tiling of the whole
plane.

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.8 (Wang tiles, valid tilings, periodic and aperiodic tile sets, NW-deterministic tile sets, and the compactness remark).
