# The every-tile-occurs tiling problem is undecidable

It is undecidable whether every tile of a finite palette $T$ occurs at the origin of some tiling of the plane by $T$. The domino problem reduces to it: adjoining to $T$ a fresh tile whose colours exceed all colours of $T$ does not change the answer, and a decider for the every-tile-occurs problem, applied to suitable sub-palettes, decides whether $T$ tiles the plane.

## Proof sketch

$T$ tiles the plane iff some nonempty sub-palette $T'\subseteq T$ has every tile occurring in tilings by $T'$ (take $T'$ the set of tiles used by a tiling); checking the finitely many sub-palettes with the hypothetical decider would decide the domino problem.

## Depends on

- [Wang tiles and tilings of the plane](wang-tiles.md)

## Proof depends on

- [Berger: the domino problem is undecidable](domino-problem-undecidable.md)

## Sources

- Robin Hirsch and Ian Hodkinson, "Representability is not Decidable for Finite Relation Algebras", Transactions of the American Mathematical Society 353(4), 2001, Section 3.
