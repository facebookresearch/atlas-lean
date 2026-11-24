# Iterates of a halted state are constant

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. Write $\hat\sigma$ for the iteration step that fixes halted states: $\hat\sigma(s) = s$ if $s$ is
halted and $\hat\sigma(s) = \sigma(s)$ otherwise.
If $s$ is halted, then $\hat\sigma^n(s) = s$ for every $n \in \mathbb{N}$.
