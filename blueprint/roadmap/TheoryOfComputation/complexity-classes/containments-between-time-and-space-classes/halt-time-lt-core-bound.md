# The first halting time is below the configuration bound

Let $M$ be a deterministic Turing machine with $k$ work tapes, a finite alphabet $\Sigma$ and a
finite set of states $Q$, let $w$ be an input and $s \in \mathbb{N}$, and suppose that for every
$t$ the computation of $M$ on $w$ visits at most $s$ work-tape cells (summed over the work tapes)
in its first $t$ steps. If $M$ first halts on $w$ at step $T$, then

$$
T < (|w| + 2)\,(|Q| + 1)\,(2s + 1)^k\,(|\Sigma| + 1)^{2s + k}.
$$

The right-hand side bounds the number of configurations of $M$ on $w$ that use at most $s$
work-tape cells: input head positions, states and work-tape contents with head positions.
