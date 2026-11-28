# Tiling the plane with translates of 8 polyominoes is undecidable

No algorithm decides, given a set of eight polyominoes, whether translated copies of them tile the plane. This proves
Ollinger's conjecture and improves his bound of eleven polyominoes.

**Theorem.** The $8$-polyomino tiling problem is undecidable: there is no algorithm which, given a set of $8$ polyominoes,
decides whether the plane can be tiled by translated copies of polyominoes from the set, in the sense of
[translational tilings](translational-tilings-by-finitely-many-tiles.md) (translations only, tiles matched by shape).

The number of polyominoes is fixed at $8$; their shapes, each given as a finite set of unit cells, are the input. For one polyomino the problem is decidable, since a
polyomino that tiles the plane by translations tiles it periodically (Beauquier and Nivat). Ollinger proved undecidability
for $11$ polyominoes, and the first author of the source earlier for $10$ and for $9$ polyominoes (the case of $9$ in a manuscript in Chinese).

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's domino problem, following Ollinger's framework: an arbitrary finite set of Wang tiles is encoded in
a single *meat* polyomino, so that a fixed number of polyominoes simulates any number of Wang tiles. The eight polyominoes
are a meat, a jaw, a filler, three teeth and two links. The simulated Wang tiles are aligned with the lattice rather than
rotated by $\pi/4$, and the colors are encoded by binary strings of normal and deeper dents on the sides of $9 \times 9$
blocks; links can only join a normal dent to a deeper one, which forces adjacent simulated edges to carry equal colors. A
tiling by the eight polyominoes exists exactly when the Wang tile set tiles the plane.

## Sources

- C. Yang, Z. Zhang, "Translational tiling with 8 polyominoes is undecidable", *Discrete & Computational Geometry* 75(4):1048–1059, 2026, doi:[10.1007/s00454-024-00706-1](https://doi.org/10.1007/s00454-024-00706-1). Numbering of the version read, arXiv:2403.13472v1 (titled "A proof of Ollinger's conjecture: undecidability of tiling the plane with a set of 8 polyominoes"): Theorem 3 (the main theorem), Theorem 2 (Ollinger's eleven polyominoes, restated with its citation), Problem 1, and Section 1 (the earlier bound of ten polyominoes and Ollinger's conjecture).
