# Tiling the plane with three polygons is undecidable

No algorithm decides whether three given simple polygons tile the plane when rotations are allowed; the problem is co-RE-complete, two
polygons already make tiling a given periodic region undecidable, and completing a partial tiling is undecidable for three fixed polygons.

A finite set of *prototiles* (simple polygons) *tiles the plane* if the plane is covered, without overlapping interiors, by congruent copies of the prototiles, obtained by translations and rotations (with or without reflections). This extends the tiling problem for [Wang tiles](wang-tiles-and-valid-tilings.md), whose
square tiles are only translated and must match colors.

A polygon is given by its angles and edge lengths. In the most general model of the source these are computable numbers, each given by a Turing machine that outputs its first $n$ bits on input $n$; the hardness constructions use angles that are rational multiples of $\pi$ and edge lengths given by constant-size radical expressions.

**Theorem (Demaine and Langerman).**

1. Given three simple polygons, deciding whether they tile the plane is co-RE-complete, and in particular undecidable (Corollary 1.6 of the source). This holds whether or not reflections are allowed, and in either input model.
2. Given two simple polygons and a periodic subset of the plane, deciding whether the two polygons tile the subset is co-RE-complete (Corollary 3.8); in the reduction the subset is the complement of a periodic arrangement of copies of a third polygon.
3. There are three fixed simple polygons for which deciding whether a given finite placement of tiles extends to a tiling of the plane is co-RE-complete (Corollary 1.4 with Theorem 1.5).
4. Deciding whether a single pentagon with computable coordinates tiles the plane is co-RE-hard (Theorem 4.2).

Whether tiling with one or two given polygons is decidable remains open. Earlier undecidability results used more tiles, such as Ollinger's five polyominoes with rotations and, for translations only,
[eight polyominoes](translational-tiling-problems/tiling-the-plane-with-8-polyominoes-is.md).

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Co-recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's tiling problem through a signed variant of Wang tiles. Given $n$ Wang tiles it constructs three polygons, one of which (a "shuriken") forms a periodic arrangement while the other two simulate the signed Wang tiles, so that the three polygons tile the plane exactly
when the Wang tiles do. Membership in co-RE is proved separately for finite sets of polygons with a connected set of preplaced tiles. Item 2 follows because the union of the shurikens and its complement are periodic, and item 3 by plugging in a fixed set of Wang tiles simulating a
universal Turing machine, such as Robinson's. A complete expansion links the reduction from Wang tiles to signed Wang tiles.

## Sources

- E. D. Demaine and S. Langerman, "Tiling with three polygons is undecidable", in *41st International Symposium on Computational Geometry (SoCG 2025)*, LIPIcs 332, paper 39, 2025, doi:10.4230/LIPIcs.SoCG.2025.39; read in arXiv:2409.11582v1: Theorems 1.1 and 1.5 and Corollaries 1.2, 1.3, 1.4 and 1.6 in Section 1, the construction of three tiles simulating signed Wang tiles in Section 3 with its main theorem and corollaries, and Theorem 4.2 on computable pentagons.
