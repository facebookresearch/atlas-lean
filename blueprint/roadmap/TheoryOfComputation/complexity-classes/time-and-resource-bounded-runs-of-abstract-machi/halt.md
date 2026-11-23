# A halted state reaches its output with any time budget

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. Say that $s$ reaches the output $b$ within time $T$ and resources $S$ if some state $t$ with
$o(t) = b$ and $\mu(t) \le S$ is reached from $s$ by at most $T$ active steps, each going from a
state $u$ that has no output and satisfies $\mu(u) \le S$ to $\sigma(u)$.
If $o(s) = b$ and $\mu(s) \le S$, then $s$ reaches the output $b$ within time $T$ and resources $S$
for every $T \in \mathbb{N}$.
