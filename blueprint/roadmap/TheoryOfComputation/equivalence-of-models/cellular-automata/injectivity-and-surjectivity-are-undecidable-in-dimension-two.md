# Injectivity and surjectivity of two-dimensional cellular automata are undecidable

There is no algorithm that decides, given a two-dimensional [cellular automaton](cellular-automata-on-z-d.md), whether it is
injective, and there is no algorithm that decides whether it is surjective (Kari). Injectivity is semi-decidable, by
searching for an inverse automaton, so the neighborhood of the inverse of an injective two-dimensional cellular automaton
cannot be bounded by a computable function of its size. The proof for injectivity reduces the tiling problem, using a
tile set whose arrows force a path through arbitrarily large squares in any region where the tiling is valid.

## Depends on

- [Cellular automata on $\mathbb{Z}^d$](cellular-automata-on-z-d.md)

## Proof depends on

- [The finite tiling problem is undecidable](../../undecidable-problems/wang-tiles/the-finite-tiling-problem-is-undecidable.md)
- [The tile set SNAKES and its plane-filling property](../../undecidable-problems/wang-tiles/the-tile-set-snakes.md)
- [The tiling problem is undecidable](../../undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)
- [Bijective cellular automata are reversible](bijective-cellular-automata-are-reversible.md)

## Sources

- J. Kari, "Theory of cellular automata: a survey", *Theoretical Computer Science* 334(1–3):3–33, 2005: Theorem 10 (Kari), the sketch of its proof, and the discussion after it of semi-algorithms and of the neighborhood of inverse automata, in Section 4; Section 2.8 on the tile set SNAKES and the finite tiling problem.
