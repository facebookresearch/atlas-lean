# Every reachable state is reached by bounded execution

Let $p$ be a URM program and $x$
an input. If a machine state $s$ is reachable from the initial state with input list $[x]$ by
steps of $p$, then for some number $t$, bounded execution for $t$ steps on the instruction codes
of $p$ from the initial coded state for $x$ gives the coded state of $s$.
