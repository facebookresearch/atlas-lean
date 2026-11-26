# Halting at a given step

A multi-tape Turing machine with $k$ work tapes, a read-only input tape and a write-only output tape (the last two present even when $k = 0$) moves deterministically from configuration to configuration. For a configuration $c$ and $t \ge 0$, the run from $c$ for $t$ steps is the configuration reached after $t$ steps. The machine started in $c$ halts at step $t$ when the run for $t$ steps is a halted configuration and the run for every smaller number of steps $s < t$ is not halted.
