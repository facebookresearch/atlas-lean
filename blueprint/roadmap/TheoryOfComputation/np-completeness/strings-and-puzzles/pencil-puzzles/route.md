# Routes of the stream in PIPE MANIA

A list $w$ of tiles is a route of the stream of a PIPE MANIA instance with target length $N$ when

- $w$ has $N$ tiles, each free and different from the source;
- if $N > 0$, the first tile is the neighbour of the source in the direction of its outlet;
- consecutive tiles (the source, then the tiles of $w$ in order) share a side;
- no piece sends the stream back: the tile at position $k$ differs from the tile at position $k + 2$;
- each tile occurs at most twice in $w$; and
- a tile traversed twice holds a cross: both passes through it are straight, and the two passes go in perpendicular directions.

Traversal $k$ ($1 \le k \le N$) is of the $k$-th tile of $w$, entered from the tile before it (the source for $k = 1$) and, when $k < N$, left towards the tile after it.
