# Circuits from dag-like Karchmer–Wigderson protocols

A *dag-like protocol* for $\mathrm{KW}$ on $U\times V$ ($U\subseteq f^{-1}(1)$, $V\subseteq f^{-1}(0)$) is a DAG whose nodes are labelled by rectangles and whose inner nodes route each pair of inputs to a child, with leaves labelled by separating indices. A dag-like protocol with $k$ inner nodes and communication $t$ (bits per step) yields a De Morgan circuit with at most $(k2^t+1)2^{t+1}$ gates that is true on $U$ and false on $V$; a monotone dag-like protocol yields a monotone circuit of the same size.

## Proof sketch

Translate each inner node into a small formula over the children according to who speaks, sharing subcircuits for nodes reached along several paths, as in the tree case of the Karchmer–Wigderson theorem.

## Depends on

- [The Karchmer–Wigderson game of a Boolean function](karchmer-wigderson-game.md)

## Proof depends on

- [Karchmer–Wigderson: formula depth equals communication complexity](karchmer-wigderson-theorem.md)

## Sources

- Jan Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", Journal of Symbolic Logic, 1997.
