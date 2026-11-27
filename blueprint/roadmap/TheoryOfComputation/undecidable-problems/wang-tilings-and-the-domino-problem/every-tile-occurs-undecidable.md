# The every-tile-occurs tiling problem is undecidable

It is undecidable whether every tile of a finite palette $T$ occurs at the origin of some tiling of the plane by $T$ (by translation, equivalently whether every tile occurs somewhere in some tiling by $T$). The domino problem Turing-reduces to it: a decider for the every-tile-occurs problem, applied to the nonempty sub-palettes of $T$, decides whether $T$ tiles the plane.

## Proof sketch

$T$ tiles the plane iff some nonempty sub-palette $T'\subseteq T$ has every tile occurring in tilings by $T'$: a tiling by $T'$ is a tiling by $T$, and conversely the set of tiles used by a tiling by $T$ is such a $T'$. Checking the finitely many sub-palettes with the hypothetical decider would decide the domino problem.

## Depends on

- [Seeded and every-tile-occurs variants of the tiling problem](wang-tiles.md)

## Proof depends on

- [The tiling problem is undecidable](../wang-tiles/the-tiling-problem-is-undecidable.md)

## Sources

- Robin Hirsch and Ian Hodkinson, "Representability is not Decidable for Finite Relation Algebras", Transactions of the American Mathematical Society 353(4), 2001, Section 3.
