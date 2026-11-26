# Cook: pyramids of height h have black pebbling price h + 2

The pyramid $\Pi_h$ has levels $0,\dots,h$ with $h+1-k$ vertices on level $k$; the vertex at position $j$ of level $k+1$ has predecessors at positions $j$ and $j+1$ of level $k$. A vertex on level $k$ is pebblable with $k+2$ pebbles, and for $h\ge 1$ the sink of $\Pi_h$ has black pebbling price exactly $h+2$ (without sliding).

## Proof sketch

The upper bound pebbles the two predecessors in turn. For the lower bound, block the column path into one predecessor and the diagonal path into the other; path blocking yields one extra pebble per level.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Proof depends on

- [Path-blocking lower bounds for black pebbling](path-blocking-lower-bound.md)

## Sources

- Stephen A. Cook, "An Observation on Time-Storage Trade Off", Journal of Computer and System Sciences 9(3), 1974.
- Jakob Nordström, "New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results", 2015.
