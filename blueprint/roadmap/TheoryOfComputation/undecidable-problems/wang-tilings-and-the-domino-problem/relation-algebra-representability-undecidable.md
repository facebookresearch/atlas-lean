# Hirsch–Hodkinson: representability of finite relation algebras is undecidable

There is no algorithm that decides, given a finite relation algebra (as an atom table), whether it is representable.

## Proof sketch

Reduce the every-tile-occurs tiling problem: from a palette build a finite relation algebra whose atoms encode tiles and grid directions; a representation is constructed step by step via a winning strategy in a two-player representation game, and winning strategies correspond exactly to tilings in which every tile occurs.

## Depends on

- [Relation algebras and representability](relation-algebra-representability.md)
- [Seeded and every-tile-occurs variants of the tiling problem](wang-tiles.md)

## Proof depends on

- [The every-tile-occurs tiling problem is undecidable](every-tile-occurs-undecidable.md)

## Sources

- Robin Hirsch and Ian Hodkinson, "Representability is not Decidable for Finite Relation Algebras", Transactions of the American Mathematical Society 353(4), 2001, Theorem 8.
