# One simulated step, running case

Let $c$ be a code, $k$ and $k'$ configurations such that
one step of $c$ from $k$ gives $k'$, $t$ a natural number, $v$ a bit, and $b$ the step bound of
$c$ at $k$. Started at the label $\mathsf{sc0}$ with state bit $v$ and the stacks of the code $c$,
the clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal
program reaches the label $\mathsf{fin}$ within $b$ steps, with some state bit and the stacks of
$c$, $t$ and $k'$ with next state and action $0$.
