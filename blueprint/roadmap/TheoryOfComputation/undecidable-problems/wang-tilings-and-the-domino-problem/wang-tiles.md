# Wang tiles and tilings of the plane

A **Wang tile** is a unit square with a colour on each edge, $t=(t_N,t_S,t_W,t_E)$. A finite set (palette) $T$ **tiles the plane** if there is $\tau:\mathbb{Z}^2\to T$ with $\tau(x,y)_E=\tau(x+1,y)_W$ and $\tau(x,y)_N=\tau(x,y+1)_S$ for all $(x,y)$ (tiles are not rotated). The **domino problem** asks whether a given finite palette tiles the plane; the **seeded** variants prescribe the tile at the origin or tile only a quadrant; the **every-tile-occurs** variant asks whether every tile of $T$ appears at the origin of some tiling by $T$.

## Sources

- Hao Wang, "Proving Theorems by Pattern Recognition II", Bell System Technical Journal 40, 1961.
- Robert Berger, "The Undecidability of the Domino Problem", Memoirs of the American Mathematical Society, 1966.
- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 1971.
