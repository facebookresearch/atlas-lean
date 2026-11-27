# Translational tiling of ℤ³ by six polycubes is undecidable

No algorithm decides, given a set of six polycubes, whether translated copies of them tile three-dimensional space. Undecidability thus holds already for a fixed number of connected tiles in dimension three.

**Theorem.** The translational tiling problem of $\mathbb{Z}^3$ with $6$ tiles is undecidable, already when every tile is a [polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md): there is no algorithm that decides, given a set $P$ of six polycubes, whether $\mathbb{Z}^3$ has a [translational tiling](translational-tilings-by-finitely-many-tiles.md) by the members of $P$ (the case $G = E = \mathbb{Z}^3$, each tile a finite subset of $\mathbb{Z}^3$), equivalently whether translated copies of the polycubes tile $\mathbb{R}^3$. Rotations and reflections are not allowed.

The source notes that the theorem gives undecidability of translational tiling of $\mathbb{Z}^n$ with a set of $6$ tiles for every $n \ge 4$ as well (Remark 2), and asks whether five tiles suffice in dimension $3$ or $4$.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's domino problem. Following Ollinger's framework for tiling the plane with a fixed number of polyominoes, and the eight-polyomino construction of Yang and Zhang, a set $W$ of Wang tiles is turned into a set $P$ of six polycubes built from $8 \times 8 \times 8$ functional cubes and half cubes carrying bumps and dents: one polycube (the *meat*) encodes all the tiles of $W$ at once, with colors encoded by half cubes attached above or below its main part, and the other five (a jaw, a filler, a tooth and two links) force the copies of the meat into an arrangement in which adjacent colors match. The third dimension replaces the rotated copies of a tile that the planar framework needs. Then $P$ tiles $\mathbb{Z}^3$ by translation if and only if $W$ tiles the plane, and since the domino problem is undecidable so is the tiling problem for six polycubes.

## Sources

- C. Yang and Z. Zhang, "Undecidability of translational tiling of the 3-dimensional space with a set of 6 polycubes", *Proceedings of the American Mathematical Society* 153(8):3541–3554, 2025, doi:[10.1090/proc/17186](https://doi.org/10.1090/proc/17186); numbering of arXiv:2408.02196v1: Theorem 4 (the main theorem) with its proof in Section 3, Remark 2 after it, and the open questions in Section 4.
