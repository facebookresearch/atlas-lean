# Output reachability via bounded iterates up to the time bound

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. Write $\hat\sigma$ for the iteration step that fixes halted states: $\hat\sigma(s) = s$ if $s$ is
halted and $\hat\sigma(s) = \sigma(s)$ otherwise. Say that $s$ reaches the output $b$ within time $T$ and resources $S$ if some state $t$ with
$o(t) = b$ and $\mu(t) \le S$ is reached from $s$ by at most $T$ active steps, each going from a
state $u$ that has no output and satisfies $\mu(u) \le S$ to $\sigma(u)$.
Then $s$ reaches $b$ within time $T$ and resources $S$ if and only if $o(\hat\sigma^T(s)) = b$ and
$\mu(\hat\sigma^n(s)) \le S$ for every $n \le T$.
