# Parity-to-Rabin conversion preserves the language

If the state space is finite, then a
parity automaton $a$ accepts the same language as its Rabin presentation: the Rabin automaton
with the same transitions and initial states as $a$ whose Rabin pairs are the pairs
$(E_i, F_i)$ for $i \in \mathbb{N}$, where $E_i$ is the set of states of priority $2i$ and
$F_i$ the set of states of priority greater than $2i$.
