# A finite path to an output bounds all iterates

Consider an abstract machine with a set of states $X$, a step map $\sigma : X \to X$, an output map
$o$ that assigns to each state either an output or nothing (a state with an output is halted), and
a measure $\mu : X \to \mathbb{N}$ of the resources a state uses. Write $\hat\sigma$ for the iteration step that fixes halted states: $\hat\sigma(s) = s$ if $s$ is
halted and $\hat\sigma(s) = \sigma(s)$ otherwise.
Suppose a state $t$ is reached from $s$ by exactly $n$ active steps, each going from a state $u$
that has no output and satisfies $\mu(u) \le S$ to $\sigma(u)$, and that $o(t) = b$ and
$\mu(t) \le S$. Then $o(\hat\sigma^T(s)) = b$ for every $T \ge n$, and
$\mu(\hat\sigma^k(s)) \le S$ for every $k \in \mathbb{N}$.
