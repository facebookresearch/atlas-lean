# Monotonicity of bounded runs in time and resources

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. For an initialization map $\iota$ from inputs to states, a run on an input $a$ succeeds with output
$b$ within time $T$ and resources $S$ if $\iota(a)$ reaches $b$ within time $T$ and resources $S$.
If the run on $a$ succeeds with output $b$ within time $T$ and resources $S$, and $T \le U$ and
$S \le R$, then it succeeds with output $b$ within time $U$ and resources $R$.
