# Deterministic and nondeterministic branching programs

A (deterministic) **branching program** on variables $x_1,\dots,x_n$ over an alphabet $\Sigma$ is a directed acyclic graph with a designated start node, in which every non-sink node is labelled by a variable index $i$ and has one outgoing arc for each $a\in\Sigma$, and every sink is labelled by an output value. On input $x$, the computation starts at the start node and follows the arc labelled $x_i$ at each node labelled $i$; the output is the label of the sink reached. Its **size** is the number of nodes. A **nondeterministic** branching program additionally allows unlabelled arcs and several arcs with the same label; it accepts $x$ if some path from the start to an accepting sink is consistent with $x$, and accepts in the parity (resp. counting) sense according to the number of such consistent paths.

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
