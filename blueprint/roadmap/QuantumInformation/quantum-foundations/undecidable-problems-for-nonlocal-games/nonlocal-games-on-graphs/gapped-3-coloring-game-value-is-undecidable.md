# The gapped promise problem for the synchronous value of the 3-coloring game is undecidable

There is a constant $\alpha \in (0, 1)$ such that, in each of the quantum, quantum-approximate and commuting-operator models, no algorithm decides whether the synchronous value of a graph's 3-coloring game equals 1 or is less than $\alpha$, given that one holds.

**Theorem (Harris).** There exists $\alpha \in (0, 1)$ such that, for each $t \in \{q, qa, qc\}$, the following promise problem is undecidable: given a finite simple undirected graph $G$ without loops, promised that the [synchronous $t$-value](synchronous-values-of-the-3-coloring-game.md) $\omega_t^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ of its 3-coloring game either equals $1$ or is less than $\alpha$, decide which case holds (Theorem 6.3 of the source).

The constant $\alpha$ is the same for the three models. For $t = q$ the source states the problem is moreover RE-hard.

## Depends on

- [Synchronous values of the 3-coloring game and non-commutative Max-3-Cut](synchronous-values-of-the-3-coloring-game.md)

## Proof depends on

- [Approximating the entangled value of a nonlocal game is undecidable](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/entangled-value-is-uncomputable.md)

## Expansion

To each synchronous game $\mathcal{G} = (I, O, \lambda)$ with $|I| = n$ and $|O| = m \ge 3$ the source computably associates a graph $G_\lambda$ and proves (Theorem 5.13) that approximately winning synchronous strategies transfer: if $\omega_t^s(\operatorname{Hom}(G_\lambda, K_3), \pi_{\mathrm{edges}}) \ge 1 - \varepsilon$ then $\omega_t^s(\mathcal{G}, \pi_u) \ge 1 - \mathrm{poly}(n, 2^m)\, \varepsilon^{1/2}$, with $\pi_u$ uniform, and a value-1 synchronous game yields a perfect strategy for the coloring game of $G_\lambda$ in the models $qa$ and $qc$ (a result of the author's earlier paper on graph homomorphism games). Since $C_{qa}^s(n, m)$ is the closure of $C_q^s(n, m)$ (Kim, Paulsen and Schafhauser), the $q$ and $qa$ values coincide. So the gapped $(1, 1 - \varepsilon)$ problem for synchronous games reduces to the gapped $(1, \alpha)$ problem for 3-coloring games, and the former is undecidable by Ji, Natarajan, Vidick, Wright and Yuen. A complete expansion also links the closure theorem $\overline{C_q^s(n, m)} = C_{qa}^s(n, m)$ and the universality of graph homomorphism games, which have no pages here.

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Theorem 6.3, Theorem 5.13 and Section 6.
