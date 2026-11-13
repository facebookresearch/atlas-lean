# The clocked loop

Let $c$ be a code, let $M$ be at least the length of the code stack of
$c$, let $k$ be a configuration whose state and cells are all at most $M$, let $t$ be a natural
number and $v$ a bit, and let $k_t$ be the result of $t$ steps of $c$ from $k$, where a halted
configuration stays put. Start the program of the clocked universal machine at label `sc0` with
variable $v$ and the stacks of $c$, the clock $t$ and $k$ (next state and action $0$). If $k_t$
has halted, then within $(t + 1) \cdot L(c, M)$ steps, where $L(c, M)$ is the loop step time,
the program reaches label `hlt` with some variable and the stacks of $c$, some clock $t'$ and
$k_t$ (next state and action $0$). If instead $c$ steps $k_t$ to $k''$, then within the same
number of steps it reaches label `tmo` with some variable and the stacks of $c$, the clock $0$
and $k''$ (next state and action $0$).
