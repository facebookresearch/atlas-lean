# Embedding a configuration into one more state

For a configuration $c$ of an
$n$-state machine, its embedding is the configuration for $n + 1$ states with the same
head position and the same tape as $c$. Its state is the state of $c$, where a working
state $q \in \{0, \dots, n - 1\}$ stays $q$ and the halt state stays the halt state.
