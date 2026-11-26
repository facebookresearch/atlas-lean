# Feasible instances of TWO-LAYER CHANNEL ROUTING

An instance $(W, m, U, L)$ of TWO-LAYER CHANNEL ROUTING is feasible when there are subgraphs $T_0, \dots, T_{m-1}$ of the integer grid (the graph on $\mathbb Z^2$ joining two points at Manhattan distance $1$, whose edges are the grid segments) such that:

- each $T_k$ has finitely many vertices and is a tree, so it has at least one vertex, and its leaves are exactly the [terminal points](terminals.md) labeled $k$, where a leaf is a vertex of $T_k$ with at most one neighbor in $T_k$; a vertex with no neighbor is a leaf, so a net with one point is routed by the one-vertex tree on it;
- every segment of every $T_k$ lies [in the channel](in-channel.md): both of its ends have $y$-coordinate between $0$ and $W$, and it is not a horizontal segment on the line $y = 0$ or on the line $y = W$ (a vertical segment may end on either line);
- whenever two different trees $T_k$ and $T_l$ share a vertex $v$, one of them [runs vertically](runs-vertically.md) and the other [runs horizontally](runs-horizontally.md) through $v$: one has two different segments at $v$ and all of its segments at $v$ vertical, the other two different segments at $v$ and all of its segments at $v$ horizontal, so each has exactly its two through-segments at $v$ in its direction.

The terminal points are read from the raw lists, so repeated coordinates are allowed here, and a terminal labeled $m$ or more constrains no tree. Feasibility does not include well-formedness; the decision problem requires both.
