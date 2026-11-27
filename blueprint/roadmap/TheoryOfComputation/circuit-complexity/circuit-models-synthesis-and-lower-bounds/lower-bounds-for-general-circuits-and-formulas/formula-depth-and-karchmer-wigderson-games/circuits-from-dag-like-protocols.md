# Circuits from dag-like Karchmer–Wigderson protocols

For disjoint $U,V\subseteq\{0,1\}^n$, a *dag-like protocol* for the Karchmer–Wigderson game on $(U,V)$ is an acyclic directed graph with one source whose leaves are labelled by formulas $u_i=1\wedge v_i=0$ or $u_i=0\wedge v_i=1$, together with a strategy assigning to each non-leaf node $x$ and each pair $u\in U$, $v\in V$ an outgoing edge, and for each pair $(u,v)$ a consistency set $F(u,v)$ of nodes that contains the source, is closed under following the strategy, and contains only leaves whose labels are valid for $(u,v)$. Its communication complexity $t$ is the least number of bits the players (each knowing a node $x$ and one input) need to decide $x\in F(u,v)$ and, for a non-leaf $x$, to compute the strategy at $x$. If such a protocol has $k$ nodes and communication complexity $t$, then there is a De Morgan circuit of size $k\cdot 2^{O(t)}$ that is true on $U$ and false on $V$; if every leaf is labelled $u_i=1\wedge v_i=0$ (a monotone protocol), the circuit can be taken monotone.

## Proof sketch

Following the strategy from a node is a local search problem whose solutions are the valid leaves. With the number of nodes reachable from $x$ as cost, the sets $F(u,v)$, costs and strategy form a polynomial local search problem of size $k$ in which every step is a $t$-bit protocol, and Razborov's circuit construction for such problems yields a separating circuit of size $k\cdot 2^{O(t)}$.

## Depends on

- [The Karchmer–Wigderson game of a Boolean function](karchmer-wigderson-game.md)
- [Dag-like protocols for search problems](../../../../communication-complexity/rectangle-partitions-and-deterministic-bounds/dag-like-protocols.md)

## Sources

- Jan Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", Journal of Symbolic Logic 62(2), 457–486, 1997 (Definition 2.2 and Theorem 2.3).
- Alexander A. Razborov, "Unprovability of Lower Bounds on Circuit Size in Certain Fragments of Bounded Arithmetic", Izvestiya: Mathematics 59(1), 205–227, 1995.
