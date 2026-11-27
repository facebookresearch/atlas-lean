# Approximating the non-commutative Max-3-Cut of a graph is uncomputable

For some constant $\alpha \in (0, 1)$, no algorithm decides whether the non-commutative (or the qc) Max-3-Cut of a given graph equals its number of edges or is less than $\alpha$ times that number, given that one of the two holds.

**Theorem (Harris).** There exists $\alpha \in (0, 1)$ such that the following promise problem is undecidable: given a finite simple undirected graph $G = (V, E)$ without loops, promised that its [non-commutative Max-3-Cut](synchronous-values-of-the-3-coloring-game.md) $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G)$ either equals $|E|$ or is less than $\alpha |E|$, decide which case holds. The same holds with the qc Max-3-Cut in place of the non-commutative Max-3-Cut (Theorem 6.4 of the source).

The source contrasts this with a known polynomial-time algorithm that approximates the non-commutative Max-3-Cut within a factor $0.864$, which it cites.

## Depends on

- [Synchronous values of the 3-coloring game and non-commutative Max-3-Cut](synchronous-values-of-the-3-coloring-game.md)

## Proof depends on

- [The gapped promise problem for the synchronous value of the 3-coloring game is undecidable](gapped-3-coloring-game-value-is-undecidable.md)

## Expansion

Theorem 6.4 restates Theorem 6.3 for $t = q$ and $t = qc$ through the identities $\operatorname{NC\text{-}Max\text{-}3\text{-}Cut}(G) = |E|\, \omega_q^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$ and qc Max-3-Cut $= |E|\, \omega_{qc}^s(\operatorname{Hom}(G, K_3), \pi_{\mathrm{edges}})$, with the same constant $\alpha$.

## Sources

- Samuel J. Harris, "Approximate quantum 3-colorings of graphs and the quantum Max 3-Cut problem", *Communications in Mathematical Physics* 407(5):91, 2026, doi:[10.1007/s00220-026-05585-6](https://doi.org/10.1007/s00220-026-05585-6). Numbering of the version read, arXiv:2412.19405v1: Theorem 6.4, Theorem 6.3 and the identities after Definition 6.2.
