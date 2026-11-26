# TWO-LAYER CHANNEL ROUTING is NP-complete

The TWO-LAYER CHANNEL ROUTING decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

The decision problem accepts exactly the encodings of the following yes-instances. Instance: a positive integer $W$, a set of grid points $P = \{(a_i, W)\} \cup \{(b_j, 0)\}$ with integer $x$-coordinates, the $a_i$ distinct and the $b_j$ distinct, and a partition of $P$ into nonempty nets $N_0, \dots, N_{m-1}$. Question: is there a reserved-layer routing, that is, finite trees $T_0, \dots, T_{m-1}$ of grid segments such that

- the leaves of each $T_k$ are exactly the points of $N_k$, where a leaf is a vertex with at most one neighbor in $T_k$, so a net with one point is routed by the one-vertex tree on it;
- every segment lies in the region $0 \le y \le W$, and no segment runs along the line $y = 0$ or the line $y = W$;
- two different trees meet only in orthogonal intersections: at every common point one tree has exactly its two vertical segments and the other exactly its two horizontal segments?

The exact conditions are those of [well-formedness](well-formed.md) and [feasibility](two-layer-channel-routing-feasible.md). $W$ is encoded in binary, each coordinate as two naturals representing their difference, and the partition as a net label below $m$ on each terminal.

## Sources

- D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [8] TWO-LAYER CHANNEL ROUTING (reference: Szymanski; transformation from 3SAT), with properties (2) and (3) from problem [7] TWO-LAYER MULTIPLE MODULE ROUTING and the reserved-layer model from Section 2.
- T. G. Szymanski, "Dogleg channel routing is NP-complete", IEEE Transactions on Computer-Aided Design of Integrated Circuits and Systems 4 (1985), 31-41, doi:10.1109/TCAD.1985.1270096.
