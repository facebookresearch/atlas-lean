# Path-blocking lower bounds for black pebbling

Say that $v$ **forces $k$ pebbles** if every pebbling of $v$ reaches a configuration with at least $k$ pebbles. If $v$ has two predecessors $u_1,u_2$ such that $u_1$ forces $k$ pebbles and every configuration at the moment $u_2$ is last pebbled before $v$ must also block every source-to-$u_1$ path by a pebble (or symmetrically), then $v$ forces $k+1$ pebbles. Consequently $\mathrm{Peb}(G,v)\ge k$ whenever $v$ forces $k$ pebbles, and the price is determined by any matching upper bound.

## Proof sketch

Consider the last time a pebble is placed on one of the predecessors before $v$ is pebbled; at that moment the other predecessor carries a pebble, and the path-blocking condition shows the pebbling of the first predecessor needed $k$ pebbles while one extra pebble was kept.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Sources

- Jakob Nordström, "New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results", 2015.
