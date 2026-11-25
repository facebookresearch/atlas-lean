# Assembling an encoded DFA is primitive recursive

Let $\alpha$ be an alphabet with a
primitive recursive encoding, and encode encoded DFAs over $\alpha$ through their start state,
accepting states and transitions. The map sending a triple $(s, F, T)$, where $s \in \mathbb{N}$,
$F$ is a list of natural numbers and $T$ is a list of pairs $((q, a), t)$ with $q, t \in \mathbb{N}$
and $a \in \alpha$, to the encoded DFA over $\alpha$ with start state $s$, accepting states $F$
and transitions $T$ is primitive recursive.
