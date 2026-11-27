# Seeded and every-tile-occurs variants of the tiling problem

Let $T$ be a tile set, with tilings and validity as in [Wang tiles and valid tilings](../wang-tiles/wang-tiles-and-valid-tilings.md). The **seeded** variants of the tiling problem take $T$ together with a seed tile $t_0\in T$ and ask whether there is a valid tiling of the plane with $t_0$ at the origin, or whether there is a map $t:\mathbb{N}^2\to T$ with $t(0,0)=t_0$ whose adjacent tiles match on every shared edge inside the quadrant (a **seeded quadrant tiling**). The **every-tile-occurs** variant asks whether every tile of $T$ appears at the origin of some valid tiling of the plane by $T$.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles/wang-tiles-and-valid-tilings.md)

## Sources

- Hao Wang, "Proving Theorems by Pattern Recognition II", Bell System Technical Journal 40, 1961.
- Robert Berger, "The Undecidability of the Domino Problem", Memoirs of the American Mathematical Society, 1966.
- Robin Hirsch and Ian Hodkinson, "Representability is not Decidable for Finite Relation Algebras", Transactions of the American Mathematical Society 353(4), 2001, Section 3.
