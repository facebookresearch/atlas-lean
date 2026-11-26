# The finite tiling problem is undecidable

Let $T$ be a set of [Wang tiles](wang-tiles-and-valid-tilings.md) containing a *blank* tile $B$ whose four edges have the same colour, so that the all-blank
tiling of the plane is valid. A *finite tiling* is a valid tiling with only finitely many non-blank tiles. It is undecidable whether
a given such $T$ admits a finite tiling other than the all-blank one, by a reduction from the halting problem of Turing machines.
Unlike the general tiling problem, this one is semi-decidable: a nontrivial finite tiling, if it exists, can be found by search.

## Depends on

- [Wang tiles and valid tilings](wang-tiles-and-valid-tilings.md)

## Proof depends on

- [Halting is undecidable](../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Section 2.8, the paragraph on the finite tiling problem (crediting J. Kari, "Reversibility and surjectivity problems of cellular automata", *Journal of Computer and System Sciences* 48 (1994)).
