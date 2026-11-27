# Nondeterministic constraint logic (AND/OR constraint graphs)

A **constraint graph** is a finite multigraph (loops and parallel edges allowed) whose edges carry nonnegative integer weights and whose vertices carry integer minimum inflows; in the AND/OR graphs below all weights lie in $\{1,2\}$ and every minimum inflow is $2$. A **configuration** orients every edge; it is **legal** if at every vertex the total weight of edges pointing into it is at least its minimum inflow. A **move** reverses a single edge and must lead to a legal configuration; reachability by moves is an equivalence relation on legal configurations. An **AND vertex** has incident weights $1,1,2$ (the weight-$2$ edge may point out only when both weight-$1$ edges point in), and an **OR vertex** has weights $2,2,2$ (at least one edge points in). The decision problems of **AND/OR NCL** ask, for an AND/OR graph: (i) configuration-to-configuration reachability; (ii) given a configuration and an edge, whether some reachable configuration reverses that edge; (iii) edge-to-edge reachability with prescribed orientations.

## Sources

- Robert A. Hearn and Erik D. Demaine, "PSPACE-completeness of sliding-block puzzles and other problems through the nondeterministic constraint logic model of computation", Theoretical Computer Science 343(1–2), 2005, Section 2.
