# Resource-bounded active step

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses.
For $S \in \mathbb{N}$, there is a resource-bounded active step from a state $s$ to a state $t$ when
$s$ has no output, $\mu(s) \le S$ and $t = \sigma(s)$.
