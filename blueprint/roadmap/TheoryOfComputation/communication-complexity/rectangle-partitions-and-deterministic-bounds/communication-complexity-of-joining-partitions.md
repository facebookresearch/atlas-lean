# Communication complexity of connectivity of joined partitions

Alice and Bob each hold a partition of a finite set $\alpha$ and want to decide whether the join of the two partitions is the one-block partition (equivalently, whether the union of two graphs whose components are the blocks is connected). Every deterministic protocol needs at least $\lceil \log_2 B_{|\alpha|} \rceil$ bits, where $B_k$ is the Bell number; the same holds for deciding whether the join has more than one block. Consequently graph connectivity, with the edges split between the players, has deterministic complexity $\Omega(n \log n)$ on $n$ vertices.

## Proof sketch

The communication matrix is the join matrix of the partition lattice, $M(\sigma, \tau) = [\sigma \vee \tau = \hat 1]$, which has full rank by the Dowling–Wilson theory of geometric lattices; apply the rank lower bound. $\log_2 B_n = \Theta(n \log n)$.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Log-rank lower bound](../deterministic-communication-protocols/log-rank-le-comm-complexity.md)

## Sources

- A. Hajnal, W. Maass and G. Turán, "On the Communication Complexity of Graph Properties", STOC 1988.
- L. Lovász and M. Saks, "Communication Complexity and Combinatorial Lattice Theory", Journal of Computer and System Sciences 47(2), 1993.
