# Approximating the non-commutative Max-3-Cut of a graph is uncomputable

No algorithm decides, given a graph and a threshold $\alpha$ that may depend on the graph, whether the non-commutative Max-3-Cut of the graph equals its number of edges or is less than $\alpha$ times that number, given that one of the two holds.

**Theorem (Harris).** The following promise problem is undecidable: given a finite simple undirected graph $G = (V, E)$ without loops and with at least one edge, and a rational $\alpha \in (0, 1)$, promised that its [non-commutative Max-3-Cut](non-commutative-max-3-cut.md) $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G)$ either equals $|E|$ or is less than $\alpha |E|$, decide which case holds (Theorem 6.4 of the source, through the proof of Theorem 6.3).

The source states Theorem 6.4 with a single constant $\alpha$, and also for the qc Max-3-Cut; its proof restates Theorem 6.3, whose threshold depends on the instance and whose proof does not cover the commuting-operator model (see [the gapped problem for the 3-coloring game](gapped-3-coloring-game-value-is-undecidable.md)). The source contrasts the result with a known polynomial-time algorithm that approximates the non-commutative Max-3-Cut within a factor $0.864$, which it cites.

## Proof sketch

The identity $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = |E|\, \omega_q^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ turns an instance $(G, \alpha)$ of the promise problem for the 3-coloring game with $t = q$ into an instance of this problem with the same graph and the same $\alpha$.

## Depends on

- [Non-commutative Max-3-Cut of a graph](non-commutative-max-3-cut.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The gapped promise problem for the synchronous value of the 3-coloring game is undecidable](gapped-3-coloring-game-value-is-undecidable.md)

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Theorem 6.4, Theorem 6.3 with its proof and the identities after Definition 6.2.
