# One simulated step, halting case

Let $c$ be a code, $k$ a configuration at which $c$ halts
(one step of $c$ from $k$ gives nothing), $t$ a natural number, $v$ a bit, and $b$ the step bound
of $c$ at $k$. Started at the label $\mathsf{sc0}$ with state bit $v$ and the stacks of the code
$c$, the clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal
program reaches the label $\mathsf{hlt}$ within $b$ steps, with some state bit and the same
stacks.
