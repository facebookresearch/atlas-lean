# Feasible instances of TWO-LAYER MULTIPLE MODULE ROUTING

An instance $(\mathcal M, P, m, B)$ of TWO-LAYER MULTIPLE MODULE ROUTING is feasible when there are subgraphs $T_0, \dots, T_{m-1}$ of the integer grid (the graph on $\mathbb Z^2$ joining two points at Manhattan distance $1$, whose edges are the grid segments) and a rectangle $R$ with integer corners $(a_1, b_1)$ and $(a_2, b_2)$, where $a_1 \le a_2$ and $b_1 \le b_2$, such that:

- the area $(a_2 - a_1)(b_2 - b_1)$ of $R$ is at most $B$;
- $R$ [includes](rect-included.md) the [rectangle](module-rect.md) $(x_1, y_1, x_2, y_2)$ of every module: $a_1 \le x_1$, $x_2 \le a_2$, $b_1 \le y_1$ and $y_2 \le b_2$;
- both ends of every segment of every $T_k$ lie in the closed region $a_1 \le x \le a_2$, $b_1 \le y \le b_2$ of $R$, and for no module do both ends lie in its closed region $x_1 \le x \le x_2$, $y_1 \le y \le y_2$, so a segment may leave a module's perimeter but never run along it;
- each $T_k$ has finitely many vertices and is a tree, so it has at least one vertex, and its leaves are exactly the [terminal points](terminals-2.md) labeled $k$, where a leaf is a vertex of $T_k$ with at most one neighbor in $T_k$; a vertex with no neighbor is a leaf, so a net with one point is routed by the one-vertex tree on it;
- whenever two different trees $T_k$ and $T_l$ share a vertex $v$, one of them [runs vertically](runs-vertically.md) and the other [runs horizontally](runs-horizontally.md) through $v$: one has two different segments at $v$ and all of its segments at $v$ vertical, the other two different segments at $v$ and all of its segments at $v$ horizontal, so each has exactly its two through-segments at $v$ in its direction.

The modules and terminals are read from the raw lists, with no check that modules are proper or disjoint or that terminals are distinct; a terminal labeled $m$ or more constrains no tree. Feasibility does not include well-formedness; the decision problem requires both.
