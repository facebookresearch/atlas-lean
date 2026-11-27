# Non-commutative Max-3-Cut of a graph

The non-commutative Max-3-Cut of a graph replaces the three colors of the classical Max-3-Cut by matrix unitaries of order 3, and equals the number of edges times the synchronous quantum value of the graph's 3-coloring game.

Let $G = (V, E)$ be a finite simple undirected graph without loops and with at least one edge.

**Definition.** The *non-commutative Max-3-Cut* of $G$ is

$$
\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = \sup \sum_{\{i, j\} \in E} \Big(1 - \frac{1}{3} \sum_{s=0}^{2} \operatorname{tr}_d\big(u_i^s (u_j^s)^*\big)\Big),
$$

the supremum over $d \in \mathbb{N}$ and families of $d \times d$ matrices $u_j$ ($j \in V$) with $u_j^* u_j = u_j^3 = I_d$, where $\operatorname{tr}_d$ is the normalized trace and each edge is counted once. The *qc Max-3-Cut* takes the same supremum over tracial von Neumann algebras $(\mathcal{M}, \tau)$ and unitaries $u_j \in \mathcal{M}$ with $u_j^3 = 1$, with $\tau$ in place of $\operatorname{tr}_d$. With $\omega = e^{2\pi i/3}$ and commuting scalar choices $u_j \in \{1, \omega, \omega^2\}$ the same expression gives the classical Max-3-Cut. One has $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = |E|\, \omega_q^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ and qc Max-3-Cut $= |E|\, \omega_{qc}^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Synchronous values of the 3-coloring game](synchronous-values-of-the-3-coloring-game.md)

## Proof depends on

None.

## Expansion

The identities between the Max-3-Cut quantities and the synchronous values (Section 6 of the source, after Definition 6.2) come from writing each order-3 unitary as $u_j = \sum_{a=0}^{2} \omega^a e_{a,j}$ with a projection-valued measure $\{e_{a,j}\}_a$: the trace term then counts the probability that the two endpoints of an edge receive the same color.

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Definition 6.2 and the identities following it in Section 6.
