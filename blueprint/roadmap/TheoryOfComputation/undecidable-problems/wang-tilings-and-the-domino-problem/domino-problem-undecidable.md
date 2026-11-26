# Berger: the domino problem is undecidable

No algorithm decides, given a finite set of Wang tiles, whether it tiles the plane. Consequently there exist aperiodic tile sets (which tile the plane but only non-periodically).

## Proof sketch

Reduce from seeded-quadrant tiling: overlay a Turing-machine-simulation layer on the Robinson hierarchy so that computations are started at the seeds of every free grid and run inside it; the free grids of all sizes force the machine to run arbitrarily long without halting, which removes the need for a seed while the Robinson layer prevents the computation layer from being trivial. If every palette that tiles had a periodic tiling, the domino problem would be decidable by enumerating both periodic tilings and failures.

## Depends on

- [Wang tiles and tilings of the plane](wang-tiles.md)

## Proof depends on

- [Seeded-quadrant Wang tiling is undecidable](seeded-quadrant-tiling-undecidable.md)
- [Robinson's aperiodic tile set and substitution hierarchy](robinson-tile-set.md)
- [Compactness for Wang tilings](wang-tiling-compactness.md)

## Sources

- Robert Berger, "The Undecidability of the Domino Problem", Memoirs of the American Mathematical Society, 1966.
- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 1971, Section 7.
- Emmanuel Jeandel and Pascal Vanier, "The Undecidability of the Domino Problem", Substitution and Tiling Dynamics: Introduction to Self-inducing Structures, 2020.
