# Legal beams in HOTARU BEAM

A list $B$ of grid points is a legal beam from the firefly $F$ to the firefly $G$ when $B$ is nonempty; its first point is one unit from $F$ in the direction of $F$'s dot; $F$ followed by $B$ is a walk of unit grid steps (successive points are orthogonally adjacent; points may repeat); every point of $B$ lies on the grid; no point of $B$ before the last is the intersection of a firefly; the last point is $G$'s intersection; the point before it (or $F$, when $B$ has one point) is not the neighbour of $G$ in the direction of $G$'s dot; and, when $F$ is numbered, the path $F, B$ has exactly that number of [bends](bends.md).

The test is local and allows repeated points: an unnumbered beam can revisit $(1, 0)$ before its final point. Repetition is forbidden by the global test in [feasibility](hotaru-beam-feasible.md), not by a ninth local condition.
