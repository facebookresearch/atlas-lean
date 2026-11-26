# Deterministic parity automata

For a type of states $S$ and an alphabet $\Sigma$, a deterministic parity automaton consists of

- a start state $s_0 \in S$;
- a deterministic transition function $\delta : S \times \Sigma \to S$;
- a priority function $\Omega : S \to \mathbb{N}$.

Its language is the set of infinite words whose unique run has priority sequence satisfying the even max-parity condition: the largest priority occurring infinitely often exists and is even.
