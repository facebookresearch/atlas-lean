# Robinson's aperiodic tile set and substitution hierarchy

There is an explicit finite Wang tile set (a corrected Robinson palette, together with shading and signal layers) that tiles the plane, such that every tiling of the plane by it has a hierarchical structure: for every $n$ it contains level-$n$ supertiles, squares of side $2^{n+1}-1$ formed by four level-$(n-1)$ supertiles in a $2\times2$ arrangement joined by a central cross, and away from at most two infinite "fault lines" (a row and a column along which the hierarchy can break) every tile lies in supertiles of all levels. In particular every tiling contains arbitrarily large marked squares ('free grids') at nested positions, which carry the Turing-machine simulation in the undecidability proof, and no tiling is periodic.

## Proof sketch

Local recognizability: on a fixed parity class of corners, each supertile boundary is determined by a constant-size neighbourhood, so a tiling can be desubstituted to a tiling by the same palette at the next level. Iterating gives a tower; periodicity would contradict the existence of supertiles of all sizes.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles/wang-tiles-and-valid-tilings.md)

## Proof depends on

- [The tiling problem is undecidable](../wang-tiles/the-tiling-problem-is-undecidable.md)

## Sources

- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 177–209, 1971 (the tile set, its macro-tiles and nonperiodicity).
- Emmanuel Jeandel and Pascal Vanier, "The Undecidability of the Domino Problem", in Substitution and Tiling Dynamics: Introduction to Self-inducing Structures, Lecture Notes in Mathematics 2273, Springer, 293–357, 2020 (a corrected and detailed account of Robinson's construction).
