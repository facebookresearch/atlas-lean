# The gapped promise problem for the synchronous value of the 3-coloring game is undecidable

In the quantum and quantum-approximate models, no algorithm decides, given a graph and a threshold $\alpha$ that may depend on the graph, whether the synchronous value of the graph's 3-coloring game equals 1 or is less than $\alpha$, given that one holds.

**Theorem (Harris).** For each $t \in \{q, qa\}$, the following promise problem is undecidable: given a finite simple undirected graph $G$ without loops and with at least one edge, and a rational $\alpha \in (0, 1)$, promised that the [synchronous $t$-value](synchronous-values-of-the-3-coloring-game.md) $\omega_t^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ of its 3-coloring game either equals $1$ or is less than $\alpha$, decide which case holds (the proof of Theorem 6.3 of the source).

The two models give the same value, since $C_{qa}^s(n, m)$ is the closure of $C_q^s(n, m)$. The threshold depends on the instance: the proof reduces a synchronous game with $n$ questions and $m$ answers to a graph $G_\lambda$ with $\alpha = 1 - (\varepsilon / h(n, 2^m))^2$, where $\varepsilon$ is the fixed gap of the starting problem and $h$ is the polynomial of Theorem 5.13, so it gives no single $\alpha$ for all graphs, although Theorem 6.3 of the source is worded with one. The source also states the result for $t = qc$; its proof takes the undecidability of the gapped problem for the commuting-operator value from the result of Ji, Natarajan, Vidick, Wright and Yuen, which concerns the tensor-product value, so the cited proof does not cover $t = qc$.

## Depends on

- [Synchronous values of the 3-coloring game](synchronous-values-of-the-3-coloring-game.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Approximating the entangled value of a nonlocal game is undecidable](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/entangled-value-is-uncomputable.md)

## Expansion

To each synchronous game $\mathcal{G} = (I, O, \lambda)$ with $|I| = n \ge 2$ and $|O| = m$ the source computably associates a graph $G_\lambda$ and proves (Theorem 5.13) that approximately winning synchronous strategies transfer: for a polynomial $h$ of two variables, if $\omega_t^s(\operatorname{Hom}(G_\lambda, K_3), \pi_{\mathrm{edges}}) \ge 1 - \varepsilon$ then $\omega_t^s(\mathcal{G}, \pi_u) \ge 1 - h(n, 2^m)\, \varepsilon^{1/2}$, with $\pi_u$ uniform; and a value-1 synchronous game yields a perfect strategy for the coloring game of $G_\lambda$ in the model $qa$ (a result of the author's earlier paper on graph homomorphism games). So the gapped $(1, 1 - \varepsilon)$ problem for the quantum value of synchronous games, undecidable by Ji, Natarajan, Vidick, Wright and Yuen, reduces to the problem above with $\alpha = 1 - (\varepsilon / h(n, 2^m))^2$; a polynomial with natural-number coefficients that dominates $h$ can replace it, which makes $\alpha$ a computable rational. A good expansion links the transfer theorem (Theorem 5.13 of the source), the closure theorem $\overline{C_q^s(n, m)} = C_{qa}^s(n, m)$ of Kim, Paulsen and Schafhauser, and the universality of graph homomorphism games.

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Theorem 6.3, Theorem 5.13 and Section 6.
