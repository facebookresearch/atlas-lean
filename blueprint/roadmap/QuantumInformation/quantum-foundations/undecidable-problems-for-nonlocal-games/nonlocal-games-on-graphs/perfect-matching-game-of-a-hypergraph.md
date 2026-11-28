# Perfect matching game of a hypergraph and quantum perfect matchings

The perfect matching game of a hypergraph asks two players, each given a vertex, to answer hyperedges containing their vertex that are equal or disjoint; a hypergraph has a quantum perfect matching when this game has a perfect finite-dimensional quantum strategy.

**The game.** Let $G = (V, E)$ be a finite [hypergraph](../../../../Combinatorics/extremal-set-theory/hypergraph-colouring-matching/erd-s-faber-lov-sz-conjecture/hypergraph.md) with vertex set $V$ and set of hyperedges $E$. The *perfect matching game* $PM_G$ is the synchronous nonlocal game with question set $V$ and answer set $E$ in which, on questions $(v_1, v_2) \in V \times V$, the players answering $(e_1, e_2) \in E \times E$ win if and only if

1. (adjacency) $v_1 \in e_1$ and $v_2 \in e_2$; and
2. (consistency and disjointness) $e_1 \cap e_2 \ne \varnothing$ implies $e_1 = e_2$.

A perfect classical strategy for $PM_G$ exists if and only if $G$ has a perfect [matching](../../../../Combinatorics/extremal-set-theory/hypergraph-colouring-matching/strong-matchings-and-covers-in-hypergraphs/is-matching.md), a set of pairwise disjoint hyperedges covering $V$ (Theorem 3.9 of the source). For a graph the hyperedges are its edges.

**Quantum perfect matching.** $G$ has a *quantum perfect matching* when $PM_G$ has a perfect [quantum strategy](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md): finite-dimensional Hilbert spaces $\mathcal{H}_A$, $\mathcal{H}_B$, a state $\psi \in \mathcal{H}_A \otimes \mathcal{H}_B$ and projective measurements for each question, winning with probability 1.

The source also states that quantum perfect matching of hypergraphs is undecidable (Theorem 6.11); its proof applies to hypergraphs the characterization of Theorem 6.4, which is proved for graphs and fails for hypergraphs. The hypergraphs on $\{1, 2, 3\}$ with edge sets $\{\{1,2,3\}, \{1,2\}\}$ and $\{\{1,2\}, \{2,3\}\}$ have the same line graph $K_2$, but only the first has a perfect matching: in the second, questions $1$ and $3$ force the intersecting answers $\{1,2\}$ and $\{2,3\}$, so not even a quantum strategy wins.

## Depends on

- [Hypergraph](../../../../Combinatorics/extremal-set-theory/hypergraph-colouring-matching/erd-s-faber-lov-sz-conjecture/hypergraph.md)
- [Matching in a hypergraph](../../../../Combinatorics/extremal-set-theory/hypergraph-colouring-matching/strong-matchings-and-covers-in-hypergraphs/is-matching.md)
- [Entangled strategies and the entangled value of a game](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/entangled-strategies-and-entangled-value.md)
- [Synchronous two-prover games](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-provers-and-the-halting-problem/synchronous-two-prover-games.md)

## Proof depends on

None.

## Sources

- David Cui, Laura Mančinska, Seyed Sajjad Nezhadi and David E. Roberson, "Quantum perfect matchings", *Annales Henri Poincaré* 27(11):4069–4094, 2026 (online 2025), doi:[10.1007/s00023-025-01632-5](https://doi.org/10.1007/s00023-025-01632-5). Numbering of the version read, arXiv:2502.05136v1: Definition 3.8, Theorem 3.9 and Definition 2.4 (quantum tensor strategies).
