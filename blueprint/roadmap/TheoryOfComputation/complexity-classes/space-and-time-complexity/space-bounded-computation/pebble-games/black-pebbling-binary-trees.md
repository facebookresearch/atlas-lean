# Black pebbling price of complete binary trees

Let $T_h$ be the complete binary tree of height $h$ with arcs from children to parents (leaves are sources, the root is the sink). A vertex at depth $d< h$ has black pebbling price $h-d+2$; in particular, for $h\ge 1$, $\mathrm{Peb}(T_h,\mathrm{root})=h+2$.

## Proof sketch

Upper bound: pebble the two children one after the other, keeping one pebble on the first child while pebbling the second recursively. Lower bound, by induction on the height: a vertex at depth $h-1$ needs three pebbles, since both of its leaf children carry pebbles when it is pebbled; above that, the two children of a vertex have disjoint ancestor sets, so the disjoint-ancestor lower bound adds one pebble per level.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Proof depends on

- [Lower bound for black pebbling from disjoint ancestor sets](path-blocking-lower-bound.md)

## Sources

- Michael S. Paterson and Carl E. Hewitt, "Comparative Schematology", Record of the Project MAC Conference on Concurrent Systems and Parallel Computation, ACM, 1970, pp. 119–127.
- Jakob Nordström, "Pebble Games, Proof Complexity, and Time-Space Trade-offs", Logical Methods in Computer Science 9(3):15, 2013.
- John E. Savage, "Models of Computation: Exploring the Power of Computing", Addison-Wesley, 1998.
