# Translational tilings by finitely many tiles

A finite family of tiles tiles a region by translations when the region is covered by translated copies of the tiles with
no overlaps. For a subset of an abelian group the tiles are finite sets; in the plane they are polyominoes.

**Tilings in an abelian group.** Let $G$ be an abelian group, $E \subseteq G$, and $F_1, \dots, F_J \subseteq G$ finite sets
(the *tiles*). A *translational tiling* of $E$ by $F_1, \dots, F_J$ is a family of sets $A_1, \dots, A_J \subseteq G$ such
that every element of $E$ can be written as $a + f$ with $a \in A_j$ and $f \in F_j$ for exactly one triple $(j, a, f)$, and
no other sums $a + f$ ($a \in A_j$, $f \in F_j$) occur; equivalently, $E$ is the disjoint union of the translates $a + F_j$,
$a \in A_j$. For $J = 1$ one says that $F = F_1$ *tiles $E$* with tiling set $A = A_1$ (a *translational monotiling*),
written

$$
A \oplus F = E .
$$

A set $E \subseteq G$ is *periodic* (strongly periodic) if it is invariant under translation by a subgroup of finite index
in $G$. For finitely generated $G$ a periodic set is described by finitely many data, so it can be part of the input of an
algorithm. A *translational tiling problem* asks, for given tiles and a given periodic region $E$, whether a translational
tiling of $E$ exists.

**Polyominoes in the plane.** A *polyomino* is a finite union of closed unit squares of the integer lattice in
$\mathbb{R}^2$ that is connected through shared edges. A finite set $P$ of polyominoes *tiles the plane by translations* if
$\mathbb{R}^2$ is a union of translated copies $v + p$ ($p \in P$, $v \in \mathbb{R}^2$), each polyomino used any number of
times, whose interiors are pairwise disjoint. For a fixed $k$, the *$k$-polyomino tiling problem* asks, given a set of $k$
polyominoes, whether it tiles the plane by translations. Only translations are allowed (no rotations or reflections), and
tiles match by shape only.

## Depends on

- [Abelian group](../../../../GroupTheory/group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

A monotiling of $G$ itself is the case $E = G$ of [tilings of an abelian group by translates](../../../../Combinatorics/tilings-board-placements/periodic-tiling-conjecture/is-tiling.md).
Golomb's encoding turns a set of Wang tiles into a set of the same number of polyominoes by bumps and dents on the sides of
large squares, so tiling problems for polyominoes with an unbounded number of tiles inherit the undecidability of the
domino problem; the results in this folder fix the number of tiles.

## Sources

- R. Greenfeld, T. Tao, "Undecidability of translational monotilings", *Journal of the European Mathematical Society*, published online 2025, doi:[10.4171/JEMS/1673](https://doi.org/10.4171/JEMS/1673). Numbering of the version read, arXiv:2309.09504v2: Section 1.1 (translational monotilings, the notation $A \oplus F = E$ and strong periodicity).
- C. Yang, Z. Zhang, "Translational tiling with 8 polyominoes is undecidable", *Discrete & Computational Geometry* 75(4):1048–1059, 2026, doi:[10.1007/s00454-024-00706-1](https://doi.org/10.1007/s00454-024-00706-1). Numbering of the version read, arXiv:2403.13472v1 (titled "A proof of Ollinger's conjecture: undecidability of tiling the plane with a set of 8 polyominoes"): Problem 1 and the description of translational polyomino tilings in Section 1.
