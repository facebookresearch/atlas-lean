# Translational tiling of four-dimensional space with three tiles is undecidable

No algorithm decides whether translated copies of three given polyhypercubes tile four-dimensional space, nor whether translated copies of four
given polycubes tile three-dimensional space.

Tiles are finite subsets of $\mathbb{Z}^n$, equivalently unions of unit cubes $\prod_{i=1}^n [z_i, z_i + 1]$ in $\mathbb{R}^n$, called *polycubes* for $n = 3$ and *polyhypercubes* for $n = 4$. A set of tiles tiles $\mathbb{Z}^n$ when
$\mathbb{Z}^n$ is the disjoint union of translates of the tiles, as for [translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md); rotations and reflections are not allowed.

**Theorem.**

1. It is undecidable, given a set of $4$ polycubes, whether translated copies of them tile $\mathbb{Z}^3$.
2. It is undecidable, given a set of $3$ polyhypercubes, whether translated copies of them tile $\mathbb{Z}^4$.

The tiles constructed in the proofs are connected. Translational tiling is decidable in dimension $1$ and for a single tile in the plane; whether it is undecidable for a single tile in some fixed dimension
remains open, while Greenfeld and Tao showed undecidability for a single tile when the dimension is part of the input.

## Depends on

- [Translational tilings by finitely many tiles](translational-tilings-by-finitely-many-tiles.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../the-tiling-problem-is-undecidable.md)

## Expansion

Item 1 reduces Wang's domino problem through a new reduction framework: from a set of Wang tiles one computes four polycubes, an encoder, two linkers and a filler, assembled from $10 \times 10 \times 10$ building blocks
whose bumps and dents force translational tilings of $\mathbb{Z}^3$ to simulate valid Wang tilings. Item 2 applies a lifting technique, reading the fourth dimension as time, to the three-dimensional tile set and its
tilings, which reduces the number of tiles by one.

## Sources

- C. Yang and Z. Zhang, "Undecidability of translational tiling with three tiles", *Mathematics of Computation*, published online 2026, doi:10.1090/mcom/4290; read in arXiv:2412.10646v1: Theorem 1 (three tiles in dimension $4$) and Theorem 2 (four tiles in dimension $3$), stated in Section 1 and proved in Sections 3 and 2 respectively, and the survey of known cases in Section 1, with the numbering of that version.
