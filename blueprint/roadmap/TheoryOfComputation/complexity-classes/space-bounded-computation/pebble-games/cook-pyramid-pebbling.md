# Cook: pyramids of height h have black pebbling price h + 2

The pyramid $\Pi_h$ has levels $0,\dots,h$ with $h+1-k$ vertices on level $k$; the vertex at position $j$ of level $k+1$ has predecessors at positions $j$ and $j+1$ of level $k$. A vertex on level $k$ is pebblable with $k+2$ pebbles, and for $h\ge 1$ the sink of $\Pi_h$ has black pebbling price exactly $h+2$ (without sliding).

## Proof sketch

The upper bound pebbles the two predecessors in turn. The lower bound is Cook's blocking argument, which uses only the shape of $\Pi_h$; the predecessors of a vertex share ancestors, so the disjoint-ancestor lower bound does not apply. Take a pebbling of the sink and the first moment $t$ at which every source-to-sink path carries a pebble, and let $P$ be a path that is blocked only at $t$. The placement at $t$ is on the source $u$ of $P$, since a placement on another vertex of $P$ needs that vertex's predecessor on $P$ to carry a pebble already. For each of the $h$ vertices $w\in P\setminus\{u\}$, the path that reaches $w$ in a straight line from a source through the predecessor of $w$ not on $P$, and then follows $P$ to the sink, is blocked before $t$ by a pebble not on $P$; two such paths meet only on $P$, so these pebbles are distinct, and $h+1$ pebbles are present at $t$. Moving the removals that follow $t$ before the placement at $t$ never raises the space, so the next move after a placement on a source may be taken to be a placement, which gives $h+2$ pebbles.

## Depends on

- [Black pebble game and black pebbling price](black-pebble-game.md)

## Sources

- Stephen A. Cook, "An Observation on Time-Storage Trade Off", Journal of Computer and System Sciences 9(3), 1974.
- Michael S. Paterson and Carl E. Hewitt, "Comparative Schematology", Record of the Project MAC Conference on Concurrent Systems and Parallel Computation, ACM, 1970, pp. 119–127.
- Jakob Nordström, "Pebble Games, Proof Complexity, and Time-Space Trade-offs", Logical Methods in Computer Science 9(3):15, 2013.
