# Reading the input

Let $c$ be a code, $x$ a list of bits and $T$ a natural number, and let
$p$ be the cost of reading the input of $c$, $x$ and $T$. Started at the label $\mathsf{pc0}$ with
state bit false, the input encoding of $c$, $x$ and $T$ on the stack $X$ and every other stack
empty, the clocked universal program reaches the label $\mathsf{sc0}$ in exactly $p$ steps, with
some state bit and the stacks of the code $c$, the clock $T$ and the initial configuration on $x$,
with next state and action $0$.
