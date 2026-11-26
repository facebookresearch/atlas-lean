# The tiling problem is undecidable

The *tiling problem* asks whether a given finite tile set admits a valid tiling of the plane, in the sense of
[Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md). There is no algorithm that decides it (Berger; a
simplified proof is due to Robinson). The complement of the problem is recursively enumerable: by compactness, a tile
set admits no valid tiling exactly when some square admits no valid tiling.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

This page becomes ready once:

- Construction of an aperiodic tile set whose valid tilings carry nested square frames in which Turing machine computations are simulated, as in Berger's and Robinson's proofs (proof prerequisite; not yet stated)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Theorem 4 (Berger and Robinson) and the compactness remark before it in Section 2.8.
