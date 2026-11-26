# Black pebbling price of complete binary trees

Let $T_h$ be the complete binary tree of height $h$ with arcs from children to parents (leaves are sources, the root is the sink). A vertex at depth $d< h$ has black pebbling price $h-d+2$; in particular, for $h\ge 1$, $\mathrm{Peb}(T_h,\mathrm{root})=h+2$.

## Proof sketch

Upper bound: pebble the two children one after the other, keeping one pebble on the first child while pebbling the second recursively. Lower bound: path blocking with the leftmost path into each child as the witness path, inductively on the height.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Proof depends on

- [Path-blocking lower bounds for black pebbling](path-blocking-lower-bound.md)

## Sources

- Jakob Nordström, "New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results", 2015.
- John E. Savage, "Models of Computation: Exploring the Power of Computing", Addison-Wesley, 1998.
