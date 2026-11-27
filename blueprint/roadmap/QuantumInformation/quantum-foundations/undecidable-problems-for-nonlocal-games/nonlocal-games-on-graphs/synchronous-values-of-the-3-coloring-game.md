# Synchronous values of the 3-coloring game and non-commutative Max-3-Cut

The 3-coloring game of a graph asks two players, each given a vertex, to answer colors that agree on equal vertices and differ on adjacent ones; its synchronous value in a model $t$ is the best winning probability of a synchronous $t$-correlation, and the non-commutative Max-3-Cut rescales the quantum one.

**The game.** Let $G = (V, E)$ be a finite simple undirected graph without loops. The 3-coloring game $\operatorname{Hom}(G, K_3)$ has question set $V$, answer set $\{1, 2, 3\}$, and rule function

$$
\lambda(a, b, x, y) = \begin{cases} 0 & \text{if } x = y \text{ and } a \ne b, \\ 0 & \text{if } x \sim y \text{ and } a = b, \\ 1 & \text{otherwise,} \end{cases}
$$

where $x \sim y$ means $(x, y) \in E$. The questions are drawn from $\pi_{\mathrm{edges}}$, the uniform distribution on ordered pairs forming edges: $\pi_{\mathrm{edges}}(x, y) = 1/(2|E|)$ if $(x, y) \in E$ and $0$ otherwise.

**Synchronous values.** A correlation $p = (p(a, b \mid x, y))$ is *synchronous* when $p(a, b \mid x, x) = 0$ for all $x$ and $a \ne b$. For $t \in \{\mathrm{loc}, q, qa, qc\}$ let $C_t^s(n, m)$ be the synchronous correlations with $n$ questions and $m$ answers in the [local, quantum, quantum-approximate or commuting-operator correlation set](../../tsirelson-problem-and-connes-embedding/quantum-correlation-sets-q-qs-qa-qc.md). The *synchronous $t$-value* of a game $\mathcal{G}$ with question distribution $\pi$ is

$$
\omega_t^s(\mathcal{G}, \pi) = \sup \Big\{ \sum_{x, y} \pi(x, y) \sum_{a, b} \lambda(a, b, x, y)\, p(a, b \mid x, y) : p \in C_t^s(n, m) \Big\}.
$$

**Non-commutative Max-3-Cut.** The *non-commutative Max-3-Cut* of $G$ is

$$
\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = \sup \sum_{\{i, j\} \in E} \Big(1 - \frac{1}{3} \sum_{s=0}^{2} \operatorname{tr}_d\big(u_i^s (u_j^s)^*\big)\Big),
$$

the supremum over $d \in \mathbb{N}$ and families of $d \times d$ matrices $u_j$ ($j \in V$) with $u_j^* u_j = u_j^3 = I_d$, where $\operatorname{tr}_d$ is the normalized trace and each edge is counted once. The *qc Max-3-Cut* takes the same supremum over tracial von Neumann algebras $(\mathcal{M}, \tau)$ and unitaries $u_j \in \mathcal{M}$ with $u_j^3 = 1$, with $\tau$ in place of $\operatorname{tr}_d$. With $\omega = e^{2\pi i/3}$ and commuting scalar choices $u_j \in \{1, \omega, \omega^2\}$ the same expression gives the classical Max-3-Cut. One has $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = |E|\, \omega_q^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ and qc Max-3-Cut $= |E|\, \omega_{qc}^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Synchronous two-prover games](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/synchronous-two-prover-games.md)
- [Quantum correlation sets C_q, C_qs, C_qa and C_qc](../../tsirelson-problem-and-connes-embedding/quantum-correlation-sets-q-qs-qa-qc.md)

## Proof depends on

None.

## Expansion

The identities between the Max-3-Cut quantities and the synchronous values (Section 6 of the source, after Definition 6.2) come from writing each order-3 unitary as $u_j = \sum_{a=0}^{2} \omega^a e_{a,j}$ with a projection-valued measure $\{e_{a,j}\}_a$: the trace term then counts the probability that the two endpoints of an edge receive the same color.

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Section 1 (the 3-coloring game and $\pi_{\mathrm{edges}}$), Definition 6.2 and the identities following it.
