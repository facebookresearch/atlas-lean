# Tiling the plane with three polygons is undecidable

No algorithm decides whether three given simple polygons tile the plane when rotations are allowed; the problem is co-RE-complete, two
polygons already make tiling a given periodic region undecidable, and completing a partial tiling is co-RE-complete for three fixed polygons.

A finite set of *prototiles* ([simple polygons](../../../ComputerScience/computational-geometry/polygons-and-triangulations/simple-polygons.md)) *tiles the plane* if the plane is covered, without overlapping interiors, by congruent copies of the prototiles, obtained by translations and rotations (with or without reflections). This extends the tiling problem for [Wang tiles](wang-tiles-and-valid-tilings.md), whose
square tiles are only translated and must match colors.

A polygon is given by its sequence of angles, measured in degrees, and edge lengths. In the most general model of the source (Definition 1 in Section 4.1) a real number $a$ is *computable* if a Turing machine $T_a$ outputs, on each positive integer $n$, an integer $T_a(n)$ with $(T_a(n) - 1)/n \le a \le (T_a(n) + 1)/n$, and a *computable polygon* is one promised to be simple and closed whose angles and edge lengths are computable, given by such machines. A polygon is *nice* if its angles are rational multiples of $\pi$ (rational numbers of degrees) and its edge lengths are given by constant-size radical expressions; the hardness constructions use nice polygons. As input, this page gives a periodic subset of the plane (the source fixes no encoding) by two linearly independent period vectors and a polygonal region whose translates by the lattice they generate make up the subset.

**Theorem (Demaine and Langerman).**

1. Given three simple polygons, deciding whether they tile the plane is co-RE-complete, and in particular undecidable, when the edge lengths and the angles measured in degrees are given as computable numbers or as constant-size radical expressions (Corollary 1.6 of the published version; with angles in radians a radical expression could not give the angles of any polygon, whose angle sum $(n-2)\pi$ is transcendental), and also for nice polygons (Corollary 3.7). This holds whether or not reflections are allowed.
2. Given two simple polygons and a periodic subset of the plane, deciding whether the two polygons tile the subset is undecidable (Corollary 1.2); for two nice polygons it is co-RE-complete (Corollary 3.8). In the reduction the subset is the complement of a periodic arrangement of copies of a third polygon.
3. There are three fixed simple polygons for which deciding whether a given finite placement of tiles extends to a tiling of the plane is co-RE-complete (Corollary 3.9).
4. Deciding whether a single computable pentagon tiles the plane is co-RE-hard (Theorem 4.2).

The source leaves open whether tiling with one or two given polygons is decidable when the polygons are given exactly, for instance as nice polygons; for computable polygons item 4 already gives co-RE-hardness with one pentagon. Earlier undecidability results used more tiles, such as Ollinger's five polyominoes with rotations and, for translations only,
[eight polyominoes](translational-tiling-problems/tiling-the-plane-with-8-polyominoes-is.md).

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)
- [Simple polygons](../../../ComputerScience/computational-geometry/polygons-and-triangulations/simple-polygons.md)
- [Co-recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces Wang's tiling problem through a signed variant of Wang tiles. Given $n$ Wang tiles it constructs three polygons, one of which (a "shuriken") forms a periodic arrangement while the other two simulate the signed Wang tiles, so that the three polygons tile the plane exactly
when the Wang tiles do. Membership in co-RE is proved separately for finite sets of polygons with a connected set of preplaced tiles. Item 2 follows because the union of the shurikens and its complement are periodic, and item 3 by plugging in a fixed set of Wang tiles simulating a
universal Turing machine, such as Robinson's. A complete expansion links the reduction from Wang tiles to signed Wang tiles.

## Sources

- E. D. Demaine and S. Langerman, "Tiling with three polygons is undecidable", in *41st International Symposium on Computational Geometry (SoCG 2025)*, LIPIcs 332, paper 39, 2025, doi:10.4230/LIPIcs.SoCG.2025.39; read in arXiv:2409.11582v1: Theorems 1.1 and 1.5 and Corollaries 1.2, 1.3, 1.4 and 1.6 in Section 1, the construction of three tiles simulating signed Wang tiles in Section 3 with Theorem 3.6 and Corollaries 3.7, 3.8 and 3.9, Definition 1 (computable numbers and polygons) in Section 4.1, and Theorem 4.2 on computable pentagons. Corollary 1.6 of the published version, LIPIcs 332, paper 39, p. 39:3, states the angles in degrees; there Definition 1 and Theorem 4.2 of the version read are Definition 4.1 and Theorem 4.3.
