# Dag-like protocols for search problems

A *dag-like protocol* (communication PLS game) for a search problem $R \subseteq X \times Y \times O$ is a directed acyclic graph $G$ with a root and leaves labelled by answers in $O$, together with, for each input pair $(x, y)$, a set $F(x, y)$ of *consistent* nodes and a strategy naming a successor of each inner node. It *solves* $R$ on $A \times B$ when, for all $(x, y) \in A \times B$, the root is in $F(x, y)$, the successor named at a consistent inner node is consistent, and a consistent leaf's answer $o$ satisfies $(x, y, o) \in R$. Its *communication complexity* $t$ is the least number such that at **every** node $v$, leaves included, the players (each knowing $v$ and their own input) can decide by a tree protocol of depth at most $t$ whether $v \in F(x, y)$ and, at an inner node, compute the successor. Its size is the number $|G|$ of nodes, and the combined measure is $|G| \cdot 2^{3t}$. Every tree protocol of depth $d$ is a dag-like protocol, with $F(x, y)$ the path of $(x, y)$ and communication complexity at most $d$.

The consistency test at the leaves must be charged: a leaf predicate may depend on both inputs, so with unbounded local communication the players could exchange their inputs inside one node and select a correct leaf for each answer, and the node count alone would say nothing. With the combined measure, a dag-like protocol of combined measure $S$ for the Karchmer–Wigderson relation of $f$ exists iff $f$ has a circuit of size $\Theta(S)$ (Razborov; monotone circuits for the monotone relation), and such protocols give interpolation lower bounds in proof complexity.

## Depends on

- [Deterministic two-party protocol](../deterministic-communication-protocols/protocol.md)
- [The Karchmer–Wigderson game of a Boolean function](../../circuit-complexity/circuit-models-synthesis-and-lower-bounds/lower-bounds-for-general-circuits-and-formulas/formula-depth-and-karchmer-wigderson-games/karchmer-wigderson-game.md)

## Sources

- S. Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", Journal of Symbolic Logic 62(2), 457–486, 1997.
- D. Sokolov, "Dag-like Communication and Its Applications", CSR 2017; ECCC report TR16-202 (Definition 3.1, following Razborov and Krajíček, with communication complexity covering the membership test at every node and size $|G| 2^{3t}$; Corollary 3.1, Razborov's correspondence with circuit size).
- A. A. Razborov, "Unprovability of Lower Bounds on Circuit Size in Certain Fragments of Bounded Arithmetic", Izvestiya: Mathematics 59(1), 1995.
