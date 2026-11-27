# Deterministic and nondeterministic branching programs

A (deterministic) **branching program** on variables $x_1,\dots,x_n$ over an alphabet $\Sigma$ is a directed acyclic graph with a designated start node, in which every non-sink node is labelled by a variable index $i$ and has one outgoing arc for each $a\in\Sigma$, and every sink is labelled by an output value. On input $x$, the computation starts at the start node and follows the arc labelled $x_i$ at each node labelled $i$; the output is the label of the sink reached. Its **size** is the number of nodes. A **nondeterministic** branching program drops the requirement of exactly one arc per symbol: a node may have several arcs with the same label (or none), and it accepts $x$ if at least one path from the start node to an accepting sink is consistent with $x$.

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity: A Modern Approach", Cambridge University Press, 2009 (web draft of 2007-01-08, Section 13.4.4).
