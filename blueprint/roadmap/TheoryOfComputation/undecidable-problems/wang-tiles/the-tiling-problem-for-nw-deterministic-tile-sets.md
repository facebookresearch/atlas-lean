# The tiling problem for NW-deterministic tile sets is undecidable

It is undecidable whether a given NW-deterministic tile set admits a valid tiling of the plane, in the sense of
[Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md); moreover, there are NW-deterministic aperiodic tile sets.
In a valid tiling by an NW-deterministic tile set each tile is determined by its northern and western neighbors, so the
tiling is a space–time diagram of a one-dimensional cellular automaton with state set $T$ whose configurations are read
along the south-west to north-east diagonals.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)

## Proof depends on

- [The tiling problem is undecidable](the-tiling-problem-is-undecidable.md)

## Expansion

This page becomes ready once:

- Kari's transformation of a tile set into an NW-deterministic one that preserves the existence of valid tilings, from J. Kari, "The nilpotency problem of one-dimensional cellular automata", *SIAM Journal on Computing* 21:571–586, 1992 (proof prerequisite and source check; not yet stated)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.8, the definition of NW-deterministic tile sets, the remark after it, and Theorem 5 (Kari).
