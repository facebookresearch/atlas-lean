# Marking shortest paths on a pushdown graph can make its monadic theory undecidable

Every pushdown graph has a decidable monadic second-order theory, but there is a pushdown graph such that marking shortest paths to the final
configurations, in any admissible way, yields a graph with an undecidable monadic second-order theory.

**Pushdown graphs.** A *deterministic real-time pushdown automaton* $\mathcal{P} = (Q, A, \Gamma, \bot, q_{\mathrm{in}}, Q_F, \delta)$, with finite sets $Q$ of states, $A$ of input letters and $\Gamma \ni \bot$ of stack symbols, has a partial transition function $\delta : Q \times \Gamma \times A \to Q \times \Gamma^{\le 2}$ that
replaces the top stack symbol, never removing or pushing the bottom symbol $\bot$. Its configurations are pairs $(q, \sigma)$ of a state and a stack content $\sigma \in (\Gamma \setminus \{\bot\})^*\bot$, the final configurations are the
$(q_f, \bot)$ with $q_f \in Q_F$, and its *configuration graph* $G_{\mathcal{P}}$ has an $a$-labeled edge from $(q, \sigma)$ to $(q', \sigma')$ when $\delta$ maps $(q, \gamma, a)$ to $(q', u)$ with $\sigma = \gamma\sigma''$ and $\sigma' = u\sigma''$. A graph with edge labels in a finite set $B$ has a *decidable monadic second-order (MSO) theory* if it is decidable whether a given MSO sentence, with an edge relation for each label in $B$, holds in it. By a theorem of
Muller and Schupp, every such configuration graph has a decidable MSO theory.

**Markings.** The *rank* of a configuration is the length of a shortest path from it to a final configuration, or $\infty$ if none exists, and $W$ is the set of configurations of finite rank. Let $\underline{a}$ be a
marked copy of each label $a$. A *well-formed marking* of $G_{\mathcal{P}}$ is a graph on the same vertices, with labels in $A \cup \underline{A}$, obtained by replacing the label $a$ of some edges by $\underline{a}$, where only
edges that decrease the rank by one may be marked and every configuration of $W$ of rank at least $1$ keeps at least one marked outgoing edge. Section 2.1 of the source writes this clause for all of $W$, but its Section 3 calls the full marking well formed although a final configuration, of rank $0$, has no marked edge; the clause is read here for the configurations of positive rank, as Section 3 uses it. Marking every rank-decreasing edge gives the full marking $\widetilde{G}_{\mathcal{P}}$.

**Theorem.** There is a pushdown automaton $\mathcal{P}$ such that every well-formed marking of $G_{\mathcal{P}}$, in particular the full marking $\widetilde{G}_{\mathcal{P}}$, has an undecidable MSO theory.

Consequently, for this $\mathcal{P}$ no well-formed marking of $G_{\mathcal{P}}$ is itself a pushdown graph, and there is a pushdown reachability game in which marking the moves of any attractor strategy, or of any
sub-strategy of one, gives a graph with an undecidable MSO theory (Corollaries 1 and 2 of the source). On this witness game, therefore, the winning strategies built by the classical constructions for pushdown games, whose markings remain pushdown graphs, are not attractor strategies.

## Depends on

- [Pushdown automaton](pushdown-automata/pda.md)
- [Arenas, strategies and memory structures](../../omega-automata-and-games/muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The stack alphabet of $\mathcal{P}$ consists of the triples in $\{1, 2, 3\}^2 \times \{2\}$ together with $\bot$, and a stack encodes the three sums $(k_1, k_2, k_3)$ of its components, hence a pair of counters $(k_1 - k_3, k_2 - k_3)$; in its first mode
$\mathcal{P}$ pushes any triple, which increments, decrements or keeps each counter. In its second mode it pops the stack through states $p_1, p_2, p_3$ at speeds that depend on the chosen component, so the marked
edges toward these states, which indicate fastest ways to a final configuration, identify the minima among $k_1, k_2, k_3$; a tie that is not a minimum, as $k_1 = k_3$ with $k_2 < k_1$, is exposed by first following a path of pushes of $(2, 3, 2)$, which raises $k_2$ above the others. An MSO sentence can then test the counters for zero and simulate any two-counter machine,
so it holds in the marked graph exactly when the machine halts. For arbitrary well-formed markings, the construction restricts attention to configurations with even sums, where equalities can still be detected. A good expansion links a page defining monadic second-order logic over edge-labelled graphs and the decidability of a structure's MSO theory (Section 2.2 of the source).

## Sources

- A. Carayol and O. Serre, "Marking shortest paths on pushdown graphs does not preserve MSO decidability", *Information Processing Letters* 116(10):638–643, 2016, doi:10.1016/j.ipl.2016.04.015; read in arXiv:1510.04000v2: Theorems 2 and 3 of Section 3 (Main results) with their proofs, the definitions of pushdown graphs, ranks and well-formed markings in Section 2.1 and Theorem 1 (Muller and Schupp) in Section 2.2, and Corollaries 1 and 2 of Section 4, with the numbering of that version.
