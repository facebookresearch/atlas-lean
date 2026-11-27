# Output reachability within time and resource bounds

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses.
For $T, S \in \mathbb{N}$ and an output $b$, a state $s$ reaches the output $b$ within time $T$ and
resources $S$ if there is a state $t$ such that $t$ is reached from $s$ by at most $T$ active steps,
each going from a state $u$ that has no output and satisfies $\mu(u) \le S$ to $\sigma(u)$, and
$o(t) = b$ and $\mu(t) \le S$.
