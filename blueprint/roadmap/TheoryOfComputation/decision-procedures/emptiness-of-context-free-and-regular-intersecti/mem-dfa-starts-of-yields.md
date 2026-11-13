# Completeness of the start states in a DFA

Let $g$ be an encoded context-free grammar and
$D$ an encoded DFA over an alphabet $T$ with decidable equality, and let $\rho$ be an encoded
right-hand side whose decoding yields a word $u$ in the grammar that $g$ denotes. If $p$ is one
of the states of $D$ and the automaton that $D$ denotes, run on $u$ from state $p$, ends in state
$q$, then $p$ is a start state of $\rho$ for $q$ given the items found for $g$ and $D$.
