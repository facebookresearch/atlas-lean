# Dag-like protocols for search problems

A *dag-like protocol* for a search problem $R \subseteq X \times Y \times O$ is a directed acyclic graph with a source and leaves labelled by answers in $O$; at each inner node $v$ the players run a deterministic tree protocol $P_v$ that decides whether $v$ is *consistent* with $(x, y)$ and, if so, names a successor. It *solves* $R$ on $A \times B$ when, for all $(x, y) \in A \times B$, the source is consistent, consistent nodes lead only to consistent nodes, and a consistent leaf's answer $o$ satisfies $(x, y, o) \in R$. Its communication complexity is the maximum depth of the $P_v$, and its size is the number of nodes. Every tree protocol is a dag-like protocol; dag-like protocols characterize circuit size via Karchmer–Wigderson relations and give interpolation lower bounds in proof complexity.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [The Karchmer–Wigderson game of a Boolean function](../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/karchmer-wigderson-game.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", Journal of Symbolic Logic 62(2), 457–486, 1997.
