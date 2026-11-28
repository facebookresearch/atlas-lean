# Translational tilings by finitely many tiles

A finite family of tiles tiles a region by translations when the region is covered by translated copies of the tiles with
no overlaps. For a subset of an abelian group the tiles are finite sets; we also consider the planar case in which the tiles are polyominoes.

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
in $G$, that is, a [periodic set](../../../../Combinatorics/tilings-board-placements/periodic-tiling-conjecture/is-periodic-tiling-set.md), a finite union of cosets of such a subgroup. As inputs of an algorithm these objects are finite data, in the following encoding chosen here (the sources do not fix one): a finite abelian group $G_0$ is given as a product $\mathbb{Z}/n_1 \times \cdots \times \mathbb{Z}/n_r$ by the list $(n_1, \dots, n_r)$, elements of $\mathbb{Z}^d \times G_0$ by their coordinates, finite sets (tiles, subsets of $G_0$) by lists of elements, and a periodic set $E \subseteq \mathbb{Z}^d$ by a basis of a sublattice $\Lambda \subseteq \mathbb{Z}^d$ of finite index together with a finite set $R$ of representatives, $E = R + \Lambda$. A polyomino is given by its finite set of unit cells. A *translational tiling problem* asks, for given tiles and a given periodic region $E$, whether a translational
tiling of $E$ exists.

**Polyominoes in the plane.** A *polyomino* is a [polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md) in dimension two, a nonempty finite set of cells of $\mathbb{Z}^2$ connected through shared edges, identified with the union of its closed unit squares in
$\mathbb{R}^2$. A finite set $P$ of polyominoes *tiles the plane by translations* if
$\mathbb{R}^2$ is a union of translated copies $v + p$ ($p \in P$, $v \in \mathbb{R}^2$), each polyomino used any number of
times, whose interiors are pairwise disjoint. For a fixed $k$, the *$k$-polyomino tiling problem* asks, given a set of $k$
polyominoes, whether it tiles the plane by translations. Only translations are allowed (no rotations or reflections), and
tiles match by shape only.

## Depends on

- [Abelian group](../../../../GroupTheory/group-basics/abelian-group.md)
- [Periodic tiling set](../../../../Combinatorics/tilings-board-placements/periodic-tiling-conjecture/is-periodic-tiling-set.md)
- [Polycube](../../../../Combinatorics/tilings-board-placements/fixed-polycubes/is-polycube-cells.md)
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
- R. Greenfeld, T. Tao, "Undecidable translational tilings with only two tiles, or one nonabelian tile", *Discrete & Computational Geometry* 70(4):1652–1706, 2023, doi:[10.1007/s00454-022-00426-4](https://doi.org/10.1007/s00454-022-00426-4). Numbering of the version read, arXiv:2108.07902v1: Section 1.4, equation (1.3) (tilings by several tiles as a disjoint union of the sets $A_j \oplus F_j$).
- C. Yang, Z. Zhang, "Translational tiling with 8 polyominoes is undecidable", *Discrete & Computational Geometry* 75(4):1048–1059, 2026, doi:[10.1007/s00454-024-00706-1](https://doi.org/10.1007/s00454-024-00706-1). Numbering of the version read, arXiv:2403.13472v1 (titled "A proof of Ollinger's conjecture: undecidability of tiling the plane with a set of 8 polyominoes"): Problem 1 and the description of translational polyomino tilings in Section 1.
