# Feasible EVEN ALTERNATING PATH (2-arc-colored digraphs) instances

A EVEN ALTERNATING PATH (2-arc-colored digraphs) instance is feasible when some simple directed
path from `s` to `t` has an even number of arcs whose colors alternate: a chain of arcs `p` from
the vertex `s` to the vertex `t` with distinct vertices, an even number `p.length - 1` of arcs,
and consecutive arcs (consecutive entries of `p.zip p.tail`) of different colors.
