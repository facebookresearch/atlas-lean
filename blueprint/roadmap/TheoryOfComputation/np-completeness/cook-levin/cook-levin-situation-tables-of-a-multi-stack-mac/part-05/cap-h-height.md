# Stack heights are at most the cap minus the window depth

Let $M$ be a finite
multi-stack Turing machine with window depth $d$, let $m$, $T$ and $t$ be natural numbers with
$t \le T$, and let $s$ be an input of length at most $m$. In the idle-extended run of $M$ from the
initial configuration on input $s$, every stack of the configuration at step $t$ has length at
most $H - d$, where $H = m + (T + 1) d + 1$ is the stack cap for input bound $m$, run length $T$
and per-step growth $d$.
