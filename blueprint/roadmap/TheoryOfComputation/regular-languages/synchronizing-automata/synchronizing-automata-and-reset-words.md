# Synchronizing automata and reset words

Let $\mathcal{A} = \langle Q, \Sigma \rangle$ be a complete deterministic finite automaton, written $q \cdot w$ for the state reached from $q$ by reading $w$. $\mathcal{A}$ is
*synchronizing* if there are a word $w \in \Sigma^*$ and a state $s$ with $q \cdot w = s$ for every $q \in Q$; such a $w$ *resets* $\mathcal{A}$ to $s$ and is a *reset word*.
The least length of a reset word is the *reset threshold* $\mathrm{rt}(\mathcal{A})$, and the *Černý function* $C(n)$ is the maximum reset threshold of a
synchronizing automaton with $n$ states.

## Sources

- M. V. Volkov, "List of results on the Černý conjecture and reset thresholds for synchronizing automata", arXiv:2508.15655v4, January 2026: Section 1.2, the definitions of synchronizing automata, reset words, the reset threshold and the Černý function.
