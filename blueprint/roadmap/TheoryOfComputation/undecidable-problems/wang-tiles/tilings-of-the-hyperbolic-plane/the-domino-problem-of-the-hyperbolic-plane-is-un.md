# The domino problem of the hyperbolic plane is undecidable

No algorithm decides whether a given finite set of tiles, all copies of the regular heptagon of the tiling $\{7,3\}$ with markings on
their sides, tiles the hyperbolic plane with matching sides.

**Theorem (Margenstern).** The domino problem of the hyperbolic plane is undecidable: there is no algorithm that, given a finite set of prototiles
whose shape is the regular heptagon of the *heptagrid*, the regular tessellation $\{7,3\}$ of the hyperbolic plane, each side carrying a
marking, decides whether the hyperbolic plane can be tiled by copies of the prototiles placed on the cells of the heptagrid so that any
two tiles sharing a side carry matching markings on it. Following Section 3.3 of the source, a copy is the image of a prototile under an isometry of the heptagrid, and only those isometries are allowed that take a tile marked $w$ or $b$ on an isocline to a tile marked $w$ or $b$ respectively on an isocline, the same one or another; the *isoclines* are the bi-infinite curves that continue the levels of the trees spanning the heptagrid (Section 2.3). This excludes rotations, which the shifts leaving the heptagrid invariant would otherwise generate. The theorem is Theorem 1 of the source.

The question is the hyperbolic analogue of Wang's general tiling problem, with no fixed initial tile; Robinson raised the general question for the hyperbolic plane in his 1971 paper and showed in 1978 that the
origin-constrained version is undecidable there. The result was first proved by Margenstern in 2008 with a different tiling. The new proof also gives a non-periodic tiling of the heptagrid built from $157$ prototiles.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles-and-valid-tilings.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof first builds an aperiodic tiling of the heptagrid with a small set of prototiles, organized into nested families of
triangle-like regions ("trees") of all sizes, as Robinson's squares are in the Euclidean plane. Inside these regions the tiles simulate the
space-time diagram of a Turing machine started on a finite initial configuration; for each machine $M$ with $I$ instructions and $\ell$
letters, $240 + 7I + 12\ell + D$ prototiles suffice when the data uses $D$ letters. The set of tiles admits a tiling exactly when the machine never
halts, so a decision procedure would solve the halting problem.

A good expansion links a page for the heptagrid (its cells, side adjacency, isometries and isoclines) with marked heptagonal tiles and their valid tilings, and a page for the aperiodic tiling of the heptagrid of Theorem 2 of the source, on which the simulation is built.

## Sources

- M. Margenstern, "The domino problem of the hyperbolic plane is undecidable: new proof", *Complex Systems* 32(1):19–56, 2023, doi:10.25088/complexsystems.32.1.19; read in arXiv:2205.07317v2: Theorem 1 (stated in the introduction), Theorem 2 (the non-periodic tiling) of Section 2, isoclines in Section 2.3, the placement convention in Section 3.3, Lemma 20 (the counting) closing the proof in Section 3, and the introduction (history and the heptagrid), with the numbering of that version.
- M. Margenstern, "The domino problem of the hyperbolic plane is undecidable", *Theoretical Computer Science* 407(1–3):29–84, 2008, doi:10.1016/j.tcs.2008.04.038 (the first proof).
