# Writing the output

Let $c$ be a code, $t$ a natural number, $k$ a configuration and $v$ a
bit, and let $N$ be the length of the cells of the head symbol of $k$ followed by the symbols to
its right (a symbol $a$ takes $a + 1$ bits). Started at the label $\mathsf{hlt}$ with state bit $v$
and the stacks of the code $c$, the clock $t$ and the configuration $k$ with next state and action
$0$, the clocked universal program reaches the label $\mathsf{done}$ within $4N + 8$ steps, with
some state bit and stacks in which the output stack $O$ holds the encoding of the output of $k$:
the bit true followed by the cells of the output of $k$.
