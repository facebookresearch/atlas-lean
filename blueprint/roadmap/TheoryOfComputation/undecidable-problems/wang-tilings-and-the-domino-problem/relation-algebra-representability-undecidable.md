# Hirsch–Hodkinson: representability of finite relation algebras is undecidable

There is no algorithm that decides, given a finite relation algebra (as an atom table), whether it is representable.

## Proof sketch

Reduce the every-tile-occurs tiling problem, normalized by adding a special tile that tiles the plane only on its own: from a palette $\tau$ with $k$ tiles build a finite weakly associative algebra $\mathrm{RA}(\tau)$ with $2k+28$ atoms encoding tiles and grid directions. A finite relation algebra is representable iff the existential player has a winning strategy in a countable representation game; a winning strategy yields, for each tile, a tiling with that tile at the origin, and conversely such tilings make $\mathrm{RA}(\tau)$ associative and give a winning strategy. Associativity of a finite weakly associative algebra is decidable, so a decision procedure for representability would decide the tiling problem.

## Depends on

- [Relation algebras and representability](relation-algebra-representability.md)
- [Seeded and every-tile-occurs variants of the tiling problem](wang-tiles.md)

## Proof depends on

- [The every-tile-occurs tiling problem is undecidable](every-tile-occurs-undecidable.md)

## Sources

- Robin Hirsch and Ian Hodkinson, "Representability is not Decidable for Finite Relation Algebras", Transactions of the American Mathematical Society 353(4), 1403–1425, 2001, Theorems 1, 3, 4 and 8.
