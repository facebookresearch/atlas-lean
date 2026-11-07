# Encoded DFA

An encoded deterministic finite automaton over an alphabet $\alpha$ is a
deterministic finite automaton given as data with natural-number states: a start state in
$\mathbb{N}$, a list of accepting states in $\mathbb{N}$, and a list of transitions $((s, a), t)$
with $s, t \in \mathbb{N}$ and $a \in \alpha$, read as "on letter $a$, state $s$ moves to $t$".
