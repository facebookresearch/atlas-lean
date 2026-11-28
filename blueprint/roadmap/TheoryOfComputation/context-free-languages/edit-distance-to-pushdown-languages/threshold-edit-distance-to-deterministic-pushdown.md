# Threshold edit distance to deterministic pushdown automata is undecidable

No algorithm decides, given a finite automaton, a deterministic pushdown automaton and an integer $k$, whether every word accepted by the first is within edit distance $k$ of a word accepted by the second.

**Theorem.** $\mathrm{TED}(\mathcal C,\mathrm{DPDA})$ is undecidable for every class $\mathcal C\in\{\mathrm{DFA},\mathrm{NFA},\mathrm{DPDA},\mathrm{PDA}\}$: already for a DFA $A_1$, there is no algorithm that, given $A_1$, a [deterministic pushdown automaton](../grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md) $A_2$ and $k\ge0$, decides whether the [edit distance](edit-distance-between-languages.md) $\mathrm{ed}(L(A_1),L(A_2))$ is at most $k$.

In the same section the source shows, by reductions from universality of PDA and from inclusion between DPDA, that $\mathrm{TED}(\mathcal C,\mathrm{PDA})$ and $\mathrm{FED}(\mathcal C,\mathrm{PDA})$ are undecidable for every such $\mathcal C$, and that $\mathrm{FED}(\mathcal C,\mathrm{DPDA})$ is undecidable for $\mathcal C\in\{\mathrm{DPDA},\mathrm{PDA}\}$. In contrast, $\mathrm{TED}(\mathcal C_1,\mathcal C_2)$ is EXPTIME-complete for $\mathcal C_1\in\{\mathrm{DPDA},\mathrm{PDA}\}$, $\mathcal C_2\in\{\mathrm{DFA},\mathrm{NFA}\}$; the status of $\mathrm{FED}(\mathrm{DFA},\mathrm{DPDA})$ is left open (conjectured coNP-complete).

## Depends on

- [Edit distance from one language to another](edit-distance-between-languages.md)
- [Deterministic pushdown automaton](../grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a context-free grammar generates every word is undecidable](../../undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-univ.md)

## Expansion

Universality of DPDA is decidable, so a direct reduction from universality is not available. A PDA is *nearly deterministic* if it has one initial state and its transitions split into a function $\delta_1$ and a set $\delta_2$ such that every accepting run takes exactly one transition of $\delta_2$. The standard reduction from the halting problem of Turing machines to universality of pushdown automata produces nearly-deterministic PDA, so universality of nearly-deterministic PDA is undecidable. The construction used for the EXPTIME lower bound of TED from pushdown to finite automata then reduces it to $\mathrm{TED}(\mathrm{DFA},\mathrm{DPDA})$: the one nondeterministic choice is replaced by an extra letter marking where it is made, which yields a DPDA $A_D$ with $L(A_N)=\Sigma^*$ iff $\mathrm{ed}(\Sigma^*,L(A_D))=1$ (inserting the marker is the single edit), and $\Sigma^*$ is recognized by a one-state DFA. Since a DFA is a special case of the other source classes, undecidability transfers to them.

## Sources

- Krishnendu Chatterjee, Thomas A. Henzinger, Rasmus Ibsen-Jensen and Jan Otop, "Edit Distance for Pushdown Automata", *Logical Methods in Computer Science* 13(3), 2017, paper 23, doi:[10.23638/LMCS-13(3:23)2017](https://doi.org/10.23638/LMCS-13(3:23)2017); numbering of arXiv:1504.08259v4 ([arXiv](https://arxiv.org/abs/1504.08259v4)): Section 5 (edit distance to PDA): Proposition 3 (TED and FED to PDA, FED to DPDA), Definition 5.1 (nearly-deterministic PDA), Lemma 5.2 (their universality), Proposition 4 (TED to DPDA) and the closing conjecture; Section 2.2 for the overview of complexity results.
