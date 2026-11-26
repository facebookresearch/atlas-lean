# TWO-LAYER MULTIPLE MODULE ROUTING is NP-complete

The TWO-LAYER MULTIPLE MODULE ROUTING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The decision problem accepts exactly the encodings of the following yes-instances. Instance: a list of modules, axis-parallel rectangles with integer corners whose lower-left corner $(x_1, y_1)$ and upper-right corner $(x_2, y_2)$ satisfy $x_1 < x_2$ and $y_1 < y_2$, any two at different list positions having disjoint closed regions; a set $P$ of distinct terminals, grid points each on the perimeter of some module; a partition of $P$ into nonempty nets $N_0, \dots, N_{m-1}$; and a nonnegative integer bound $B$. Question: is there a reserved-layer routing enclosed in a rectangle of area at most $B$, that is, finite trees $T_0, \dots, T_{m-1}$ of grid segments and an axis-parallel rectangle $R$ with integer corners and area at most $B$ such that

- $R$ includes every module and both ends of every segment, and no segment has both ends in the closed region of one module;
- the leaves of each $T_k$ are exactly the points of $N_k$, where a leaf is a vertex with at most one neighbor in $T_k$, so a net with one point is routed by the one-vertex tree on it;
- two different trees meet only in orthogonal intersections: at every common point one tree has exactly its two vertical segments and the other exactly its two horizontal segments?

The exact conditions are those of [well-formedness](well-formed-2.md) and [feasibility](two-layer-multiple-module-routing-feasib.md). $B$ is encoded in binary, each coordinate as two naturals representing their difference, and the partition as a net label below $m$ on each terminal.

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [7] TWO-LAYER MULTIPLE MODULE ROUTING (reference: T. G. Szymanski, "Dogleg channel routing is NP-complete", manuscript (1982); transformation from 3SAT) and the reserved-layer model of Section 2.
