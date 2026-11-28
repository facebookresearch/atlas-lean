# Marking shortest paths on a pushdown graph can make its monadic theory undecidable

Every pushdown graph has a decidable monadic second-order theory, but there is a pushdown graph such that marking shortest paths to the final
configurations, in any admissible way, yields a graph with an undecidable monadic second-order theory.

**Pushdown graphs.** A *deterministic real-time pushdown automaton* $\mathcal{P} = (Q, A, \Gamma, \bot, q_{\mathrm{in}}, Q_F, \delta)$ has a partial transition function $\delta : Q \times \Gamma \times A \to Q \times \Gamma^{\le 2}$ that
replaces the top stack symbol, never removing or pushing the bottom symbol $\bot$. Its configurations are pairs $(q, \sigma)$ of a state and a stack content ending in $\bot$, the final configurations are the
$(q_f, \bot)$ with $q_f \in Q_F$, and its *configuration graph* $G_{\mathcal{P}}$ has an $a$-labeled edge from $(q, \sigma)$ to $(q', \sigma')$ when $\delta$ maps $(q, \gamma, a)$ to $(q', u)$ with $\sigma = \gamma\sigma''$ and $\sigma' = u\sigma''$. By a theorem of
Muller and Schupp, every such graph has a decidable monadic second-order (MSO) theory, in the logic with edge relations for each label.

**Markings.** The *rank* of a configuration is the length of a shortest path from it to a final configuration, or $\infty$ if none exists, and $W$ is the set of configurations of finite rank. Let $\underline{a}$ be a
marked copy of each label $a$. A *well-formed marking* of $G_{\mathcal{P}}$ is a graph on the same vertices, with labels in $A \cup \underline{A}$, obtained by replacing the label $a$ of some edges by $\underline{a}$, where only
edges that decrease the rank by one may be marked and every configuration of $W$ keeps at least one marked outgoing edge. Marking every rank-decreasing edge gives the full marking $\widetilde{G}_{\mathcal{P}}$.

**Theorem.** There is a pushdown automaton $\mathcal{P}$ such that every well-formed marking of $G_{\mathcal{P}}$, in particular the full marking $\widetilde{G}_{\mathcal{P}}$, has an undecidable MSO theory.

Consequently, for this $\mathcal{P}$ no well-formed marking of $G_{\mathcal{P}}$ is itself a pushdown graph, and there is a pushdown reachability game in which marking the moves of any attractor strategy, or of any
sub-strategy of one, gives a graph with an undecidable MSO theory. The winning strategies built by the classical constructions for pushdown games are therefore not attractor strategies.

## Depends on

- [Pushdown automaton](pushdown-automata/pda.md)
- [Arenas, strategies and memory structures](../../omega-automata-and-games/muller-rabin-and-streett-games/arenas-strategies-and-memory-structures.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The stack alphabet of $\mathcal{P}$ consists of triples in $\{1, 2, 3\}^2 \times \{2\}$, and a stack encodes the three sums $(k_1, k_2, k_3)$ of its components, hence a pair of counters $(k_1 - k_3, k_2 - k_3)$; in its first mode
$\mathcal{P}$ pushes any triple, which increments, decrements or keeps each counter. In its second mode it pops the stack through states $p_1, p_2, p_3$ at speeds that depend on the chosen component, so the marked
edges toward these states, which indicate the fastest ways to a final configuration, reveal which of $k_1, k_2, k_3$ are equal. An MSO sentence can then test the counters for zero and simulate any two-counter machine,
so it holds in the marked graph exactly when the machine halts. For arbitrary well-formed markings, the construction restricts attention to configurations with even sums, where equalities can still be detected.

## Sources

- A. Carayol and O. Serre, "Marking shortest paths on pushdown graphs does not preserve MSO decidability", *Information Processing Letters* 116(10):638–643, 2016, doi:10.1016/j.ipl.2016.04.015; read in arXiv:1510.04000v2: Theorems 2 and 3 of Section 3 (Main results) with their proofs, the definitions of pushdown graphs, ranks and well-formed markings in Section 2.1 and Theorem 1 (Muller and Schupp) in Section 2.2, and Corollaries 1 and 2 of Section 4, with the numbering of that version.
