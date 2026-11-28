# Feasible GENERAL ROUTING instances

A GENERAL ROUTING instance is feasible when some closed walk visits every required vertex, traverses every required edge, and has total length at most $B$. Each traversal is charged the length of the **first** entry of the edge list whose unordered endpoints match the step: a required out-and-back on one edge listed with lengths $1$ and then $9$ costs $2$, while the reversed list costs $18$. On validated input each edge is listed once, so the charge is its length.
