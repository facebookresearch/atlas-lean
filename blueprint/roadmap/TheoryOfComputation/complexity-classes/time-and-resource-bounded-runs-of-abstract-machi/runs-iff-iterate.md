# Characterization of bounded runs by initialized iteration

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. Write $\hat\sigma$ for the iteration step that fixes halted states: $\hat\sigma(s) = s$ if $s$ is
halted and $\hat\sigma(s) = \sigma(s)$ otherwise. For an initialization map $\iota$ from inputs to states, a run on an input $a$ succeeds with output
$b$ within time $T$ and resources $S$ if $\iota(a)$ reaches $b$ within time $T$ and resources $S$.
Then the run on $a$ succeeds with output $b$ within time $T$ and resources $S$ if and only if
$o(\hat\sigma^T(\iota(a))) = b$ and $\mu(\hat\sigma^n(\iota(a))) \le S$ for every $n \in \mathbb{N}$.
