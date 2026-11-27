# Feasible DIRECTED SUBGRAPH ISOMORPHISM (G acyclic, H a directed tree) instances

An instance is feasible when there is a one-to-one map $f$ from all declared pattern vertices $0, \dots, k-1$ of $H$ to the vertices of $G$ such that, for each listed pattern arc $(a, b)$ **with both ends in range** ($a, b < k$), the pair $(f(a), f(b))$ occurs in the arc list of $G$. A listed pattern entry with an end out of range imposes nothing: with one vertex on each side, the pattern entry $(0, 1)$ is no test.
