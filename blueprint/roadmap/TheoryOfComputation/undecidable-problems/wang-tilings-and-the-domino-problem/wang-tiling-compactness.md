# Compactness for Wang tilings

A finite set of Wang tiles tiles the plane iff it tiles every finite $n\times n$ square (with matching colours inside the square). Consequently the set of palettes that do **not** tile the plane is recursively enumerable, and the domino problem is co-r.e.

## Proof sketch

König's lemma on the finitely branching tree of tilings of growing centred squares, ordered by restriction, gives an infinite branch, i.e. a tiling of $\mathbb{Z}^2$. A palette that fails is refuted by finite search over squares.

## Depends on

- [Wang tiles and valid tilings](../wang-tiles/wang-tiles-and-valid-tilings.md)

## Sources

- Raphael M. Robinson, "Undecidability and Nonperiodicity for Tilings of the Plane", Inventiones Mathematicae 12(3), 1971.
- Emmanuel Jeandel and Pascal Vanier, "The Undecidability of the Domino Problem", Substitution and Tiling Dynamics: Introduction to Self-inducing Structures, 2020.
