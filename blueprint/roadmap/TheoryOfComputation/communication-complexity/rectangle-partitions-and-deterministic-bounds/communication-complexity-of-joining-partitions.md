# Communication complexity of connectivity of joined partitions

Alice and Bob each hold a partition of a finite nonempty set $\alpha$ and want to decide whether the join of the two partitions is the one-block partition (equivalently, whether the union of two graphs whose components are the blocks is connected). Every deterministic protocol needs at least $\lceil \log_2 B_{|\alpha|} \rceil$ bits, where $B_k$ is the Bell number; the same holds for deciding whether the join has more than one block. Consequently graph connectivity, with the edges split between the players, has deterministic complexity $\Omega(n \log n)$ on $n$ vertices.

## Proof sketch

The communication matrix is the join matrix of the partition lattice, $M(\sigma, \tau) = [\sigma \vee \tau = \hat 1]$. Over $\mathbb{Q}$ it factors as $M = Z\, \mathrm{diag}\big(\mu(\pi, \hat 1)\big)\, Z^{\mathsf T}$ with $Z(\sigma, \pi) = [\sigma \le \pi]$ (refinement order): indeed $\sum_{\pi} [\sigma \le \pi][\tau \le \pi]\, \mu(\pi, \hat 1) = \sum_{\sigma \vee \tau \le \pi \le \hat 1} \mu(\pi, \hat 1) = [\sigma \vee \tau = \hat 1]$ by the defining property of the Möbius function. $Z$ is unitriangular in a linear extension of the refinement order, and $\mu(\pi, \hat 1) = (-1)^{b-1}(b-1)! \ne 0$ when $\pi$ has $b$ blocks, because the interval $[\pi, \hat 1]$ is isomorphic to the partition lattice of a $b$-element set. So $M$ has full rank $B_{|\alpha|}$; apply the log-rank lower bound, and negate the output for the second problem. Finally $\log_2 B_n = \Theta(n \log n)$.

## Depends on

- [Communication matrix](../deterministic-communication-protocols/comm-matrix.md)
- [Deterministic communication complexity](../deterministic-communication-protocols/comm-complexity.md)

## Proof depends on

- [Möbius inversion formula](../../../Order/ordered-sets/incidence-algebras-and-the-m-bius-function/moebius-inversion-iff.md)
- [Log-rank lower bound](../deterministic-communication-protocols/log-rank-le-comm-complexity.md)

## Sources

- A. Hajnal, W. Maass and G. Turán, "On the Communication Complexity of Graph Properties", STOC 1988.
- L. Lovász and M. Saks, "Communication Complexity and Combinatorial Lattice Theory", Journal of Computer and System Sciences 47(2), 1993 (the rank of the join matrix of a lattice via the Möbius function).
- R. P. Stanley, "Enumerative Combinatorics, Volume 1", Cambridge University Press, 2nd ed., 2012 (Chapter 3: the Möbius function of the partition lattice).
