# Quantum commuting isomorphism of graphs

Two graphs are quantum commuting isomorphic when the $(G,H)$-isomorphism game, in which each player receives a vertex of either graph and must answer with a vertex of the other graph preserving equality and adjacency, has a perfect commuting-operator strategy.

**Graphs.** $G$ and $H$ are finite, undirected, loopless simple graphs. For vertices $x, y$ of one graph, $\mathrm{rel}(x, y)$ records whether $x = y$, whether $x$ and $y$ are adjacent, or whether they are distinct and non-adjacent.

**The $(G,H)$-isomorphism game.** Both players' question and answer sets are $V(G) \sqcup V(H)$, and question pairs are drawn uniformly. Alice receives $x_A$ and answers $y_A$; Bob receives $x_B$ and answers $y_B$. They win when

1. each answers with a vertex of the graph the question did not come from: $x_A \in V(G) \Leftrightarrow y_A \in V(H)$ and $x_B \in V(G) \Leftrightarrow y_B \in V(H)$; and
2. writing $g_A$ for the vertex of $G$ among $x_A, y_A$, and $g_B$, $h_A$, $h_B$ likewise, $\mathrm{rel}(g_A, g_B) = \mathrm{rel}(h_A, h_B)$.

A strategy is *perfect* when it wins with probability 1. A perfect classical strategy exists exactly when $G$ and $H$ are [isomorphic](../../../../TheoryOfComputation/descriptive-complexity/fagin-s-theorem/fagin-iso.md).

**Quantum commuting isomorphism.** $G$ and $H$ are *quantum commuting isomorphic*, written $G \cong_{qc} H$, when the $(G,H)$-isomorphism game has a perfect [commuting-operator strategy](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md): a state on a possibly infinite-dimensional Hilbert space and projective measurements for Alice and Bob whose operators commute with each other. Isomorphism implies quantum isomorphism (a perfect finite-dimensional tensor-product strategy), which implies quantum commuting isomorphism, which implies nonsignaling isomorphism, and none of these implications reverses.

Equivalently (Theorem 5.13 of the source), $G \cong_{qc} H$ if and only if some unital [C\*-algebra](../../../../Analysis/operator-algebras/cstar-algebra.md) with a faithful tracial state contains projections $E_{gh}$, for $g \in V(G)$ and $h \in V(H)$, with $\sum_{h} E_{gh} = I$ for every $g$, $\sum_{g} E_{gh} = I$ for every $h$, and $E_{gh} E_{g'h'} = 0$ whenever $\operatorname{rel}(g, g') \ne \operatorname{rel}(h, h')$.

The algebraic characterization follows from the description of perfect commuting-operator strategies of synchronous games by tracial states on the game algebra (Lemma 5.12 of the source): the isomorphism game is synchronous, a perfect strategy is given by projections $E_{xy}$ in a C\*-algebra with a faithful tracial state, and the winning conditions translate into the three families of relations.

## Depends on

- [Finite simple graph](../../../../GraphTheory/planar-graphs-and-minors/graph-minors/fin-graph.md)
- [Isomorphic graphs](../../../../TheoryOfComputation/descriptive-complexity/fagin-s-theorem/fagin-iso.md)
- [Commuting-operator strategies and value](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/commuting-operator-strategies-and-value.md)
- [C\*-algebra, not necessarily with an identity element](../../../../Analysis/operator-algebras/cstar-algebra.md)

## Proof depends on

- [Perfect commuting strategies and the synchronous game algebra](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/entangled-nonlocal-games/perfect-strategies-and-synchronous-game-algebra.md)

## Sources

- Albert Atserias, Laura Mančinska, David E. Roberson, Robert Šámal, Simone Severini and Antonios Varvitsiotis, "Quantum and non-signalling graph isomorphisms", *Journal of Combinatorial Theory, Series B* 136:289–328, 2019, doi:[10.1016/j.jctb.2018.11.002](https://doi.org/10.1016/j.jctb.2018.11.002). Numbering of the version read, arXiv:1611.09837v3: Section 1.1 (the isomorphism game), Section 5.4, Lemma 5.12 and Theorem 5.13.
