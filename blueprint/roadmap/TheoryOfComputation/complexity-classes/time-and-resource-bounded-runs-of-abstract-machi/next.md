# One iteration step with absorbing halted states

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses.
The iteration step $\hat\sigma : X \to X$ sends a halted state $s$ to itself and a state $s$ without
an output to $\sigma(s)$.
