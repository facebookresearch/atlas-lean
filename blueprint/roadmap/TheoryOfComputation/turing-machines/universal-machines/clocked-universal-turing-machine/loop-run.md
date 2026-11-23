# The clocked loop

Let $c$ be a code and $M$ a natural number at least the length of the code stack of $c$. Let $k$
be a configuration bounded by $M$ (its state, its head cell and all its other cells are at most
$M$), $t$ a natural number and $v$ a bit, and let $k_t$ be the configuration obtained from $k$ by
$t$ steps of $c$, where a configuration without a step stays put. Start the clocked universal
program at the label $\mathsf{sc0}$ with state bit $v$ and the stacks of the code $c$, the clock
$t$ and the configuration $k$ with next state and action $0$, and let $L(c, M)$ be the loop step
time.

- If $c$ has no step from $k_t$, the program reaches the label $\mathsf{hlt}$ within
  $(t + 1) \cdot L(c, M)$ steps, with some state bit and the stacks of $c$, some clock $t'$ and
  $k_t$ with next state and action $0$.
- If one step of $c$ takes $k_t$ to $k''$, the program reaches the label $\mathsf{tmo}$ within
  $(t + 1) \cdot L(c, M)$ steps, with some state bit and the stacks of $c$, the clock $0$ and
  $k''$ with next state and action $0$.
