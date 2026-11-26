# Planar CSPs over even delta-matroids reduce to edge CSPs

If every relation of a finite Boolean language $\Gamma$ is an even delta-matroid, then $\mathrm{PlanarCSP}(\Gamma)$ is decidable in polynomial time. Dvořák and Kupec reduce a planar instance to an edge instance over even delta-matroids by passing to a planar dual in which the face values around each constraint are related through cyclic differences, after which the edge-CSP algorithm applies.

## Proof sketch

In a plane embedding, assign values to faces so that the original values are differences of adjacent face values; the resulting instance has every face-variable in exactly two constraints, its constraint relations are even delta-matroids, and auxiliary parity constraints are replaced by chains of width-three parity tables.

## Depends on

- [Planar Boolean CSP](planar-boolean-csp.md)
- [Delta-matroids and even delta-matroids](delta-matroids-and-even-delta-matroids.md)

## Proof depends on

- [Kazda–Kolmogorov–Rolínek: edge CSPs with even delta-matroid constraints are polynomial-time solvable](kazda-kolmogorov-rolinek-edge-csp.md)

## Sources

- Z. Dvořák and M. Kupec, "On Planar Boolean CSP", Automata, Languages, and Programming — ICALP 2015, Part I, LNCS 9134, 432–443, 2015.
- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019.
