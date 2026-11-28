# Synchronizability of deterministic one-counter automata is undecidable

Whether some input word drives every state of a real-time deterministic pushdown automaton, started with an empty stack, into one common state is undecidable, already for deterministic one-counter automata and in each of the three stack models, in contrast with the polynomial-time synchronizability of finite automata.

**Theorem.** A (real-time) *deterministic pushdown automaton* (DPDA) $M = (Q, \Sigma, \Gamma, \delta, \bot)$ has finite sets $Q$ of states, $\Sigma$ of input letters and $\Gamma$ of stack symbols, a bottom symbol $\bot \in \Gamma$ that only occurs at the bottom of the stack, and a transition function $\delta : Q \times \Sigma \times \Gamma \to Q \times \Gamma^*$ reading the top stack symbol, with no $\varepsilon$-transitions; it is a *deterministic one-counter automaton* (DCA) if $\Gamma = \{1, \bot\}$. A word $w \in \Sigma^*$ *synchronizes* $M$ if there is a state $\hat q$ such that, for every $q \in Q$, the run on $w$ from the configuration $(q, \bot)$ ends in $\hat q$ with some stack content $v_q$; it does so in the *empty stack model* if all $v_q = \bot$, in the *same stack model* if all $v_q$ are equal, and in the *arbitrary stack model* with no condition on the $v_q$. For each of the three models, there is no algorithm that decides, given a DCA (and hence, given a DPDA), whether some word synchronizes it.

Here the turn restrictions concern the synchronizing word, not the automaton: a word $w$ is $n$-turn synchronizing if, from every state, the run on $w$ makes at most $n$ turns (consists of at most $n + 1$ strokes; Definition 8 of the source). Whether a DPDA has a one-turn synchronizing word is undecidable in all three models, and whether it has a zero-turn synchronizing word is undecidable in the same stack model (Theorems 12 and 13); synchronizability is decidable for deterministic partially blind counter automata (Theorem 7), and whether a DCA has a one-turn synchronizing word is PSPACE-complete (Table 1 of the source, with membership in Theorem 17).

## Depends on

- [Synchronizing automata and reset words](synchronizing-automata-and-reset-words.md)
- [Deterministic pushdown automaton](../../context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces nonemptiness of $L(M_1) \cap L(M_2)$ for real-time DCAs $M_1, M_2$ over $\Sigma$, which is undecidable. The DCA $M_S$ contains copies of $M_1$ and $M_2$, two trap states $q_{f_1}, q_{f_2}$, a sink $q_s$ and two fresh letters $a, b$. The letter $a$ resets every state of $M_i$, and $q_{f_i}$ when the counter is empty, to the initial state of $M_i$; from a non-trap state, $a$ with a nonempty counter, and $b$ from a non-final state, lead to $q_{f_i}$ with a nonempty counter, from which $q_{f_i}$ can never be left; $b$ from a final state of $M_i$ leads to $q_s$, which only empties its counter. If $w \in L(M_1) \cap L(M_2)$, then $a w b$ followed by enough $b$'s synchronizes $M_S$ into $q_s$ with empty stack. Conversely a synchronizing word must start with $a$ and its segment between the last $a$ and the first $b$ is accepted by both automata. The same construction works in the same and arbitrary stack models. A good expansion links a page for the undecidability of nonemptiness of the intersection of the languages of two real-time deterministic one-counter automata.

## Sources

- H. Fernau, P. Wolf and T. Yamakami, "Synchronizing deterministic push-down automata can be really hard", *Information and Computation* 295, 2023, article 105089, doi:[10.1016/j.ic.2023.105089](https://doi.org/10.1016/j.ic.2023.105089); read as arXiv:2005.01381v3, whose numbering is used here: Section 2 (DPDAs, the three stack models, Definition 1), Theorem 5 with its proof, Corollary 6, Table 1, and Theorems 7, 12, 13 and 17.
