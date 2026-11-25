# Writing a timeout

Let $c$ be a code, $t$ a natural number, $k$ a configuration and $v$ a
bit. Started at the label $\mathsf{tmo}$ with state bit $v$ and the stacks of the code $c$, the
clock $t$ and the configuration $k$ with next state and action $0$, the clocked universal program
reaches the label $\mathsf{done}$ in exactly one step, with the same state bit and the same stacks
except that the output stack $O$ holds the timeout encoding, the single bit false.
