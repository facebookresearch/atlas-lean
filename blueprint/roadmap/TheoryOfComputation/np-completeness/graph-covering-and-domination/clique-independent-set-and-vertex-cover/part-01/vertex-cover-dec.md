# The VERTEX-COVER problem

The decision problem that accepts a bit string exactly when it
encodes an instance $(k, G)$, where $G$ is a simple graph on $n$ vertices, and $G$ has a vertex
cover of exactly $k$ vertices. The encoding is $k$ ones, a zero, $n$ ones, a zero, then one bit
for each pair $(i, j)$ with $i < j < n$, listed by $i$ ascending and, for each $i$, by $j$
descending, a true bit meaning that $i$ and $j$ are adjacent; a string with any other number of
pair bits is rejected.

This is Sipser's $k$-node vertex cover; for $k \le n$ it is the same as a cover of at most $k$
vertices.
