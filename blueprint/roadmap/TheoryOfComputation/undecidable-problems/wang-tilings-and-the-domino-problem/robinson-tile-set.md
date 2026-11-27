# Robinson's aperiodic tile set and substitution hierarchy

There is an explicit finite Wang tile set (a corrected Robinson palette, together with shading and signal layers) that tiles the plane, such that every tiling of the plane by it has a hierarchical structure: it decomposes uniquely into supertiles of every level $n$, each of side $2^{n+1}-1$ and formed by four level-$(n-1)$ supertiles in a $2\times2$ arrangement joined by a central cross, every matching plane has a matching substitution parent, and every tile type occurs at every level of the resulting tower. In particular every tiling contains arbitrarily large marked square 'free grids' at prescribed nested positions, and no tiling is periodic.

## Proof sketch

Local recognizability: on a fixed parity class of corners, each supertile boundary is determined by a constant-size neighbourhood, so a tiling can be desubstituted to a tiling by the same palette at the next level. Iterating gives a tower; periodicity would contradict the existence of supertiles of all sizes.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles/wang-tiles-and-valid-tilings.md)

## Proof depends on

- [Compactness for Wang tilings](wang-tiling-compactness.md)

## Sources

- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 1971.
- Emmanuel Jeandel and Pascal Vanier, "The Undecidability of the Domino Problem", Substitution and Tiling Dynamics: Introduction to Self-inducing Structures, 2020.
