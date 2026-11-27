# Quantum perfect matching of hypergraphs is undecidable

No algorithm decides, given a finite hypergraph, whether its perfect matching game has a perfect finite-dimensional quantum strategy.

**Theorem (Cui, Mančinska, Nezhadi and Roberson).** It is undecidable to decide whether a given finite hypergraph has a [quantum perfect matching](perfect-matching-game-of-a-hypergraph.md) (Theorem 6.11 of the source).

For graphs, as opposed to hypergraphs, the source leaves open whether quantum perfect matching is decidable.

## Depends on

- [Perfect matching game of a hypergraph and quantum perfect matchings](perfect-matching-game-of-a-hypergraph.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Theorem 6.4 of the source characterizes a quantum perfect matching of a graph $G$ by the quantum independence number of $2L(G)$, two disjoint copies of its line graph: $G$ has one if and only if $\alpha_q(2L(G)) = |V(G)|$; the proof of Theorem 6.11 applies this to hypergraphs. Every graph is the line graph of some hypergraph, so deciding quantum perfect matching for hypergraphs is equivalent to a quantum independence number problem for arbitrary graphs, which the source attributes to Harris as undecidable. A complete expansion links the undecidability of that quantum independence number problem (Harris, universality of graph homomorphism games and the quantum coloring problem) and the realization of every graph as a line graph of a hypergraph; neither has a page here.

## Sources

- David Cui, Laura Mančinska, Seyed Sajjad Nezhadi and David E. Roberson, "Quantum perfect matchings", *Annales Henri Poincaré* 27(11):4069–4094, 2026 (online 2025), doi:[10.1007/s00023-025-01632-5](https://doi.org/10.1007/s00023-025-01632-5). Numbering of the version read, arXiv:2502.05136v1: Theorem 6.11 and its proof, Theorem 6.4.
