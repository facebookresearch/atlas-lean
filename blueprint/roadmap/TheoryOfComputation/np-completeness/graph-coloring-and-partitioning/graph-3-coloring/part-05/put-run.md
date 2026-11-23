# Recording the current occurrence

Let $m$ be a quiescent state of the 3-COLOR emitter
with next free vertex $n$, whose name stack holds the name bits of a variable $x$ and whose
polarity stack holds only the marker for polarity $b$. From the label $\mathsf{putN}$, with
any local state, the machine runs in exactly $2n + 2|w| + 5$ steps, where $w$ is the binary
encoding of $x$, to the label $\mathsf{aft}$, in some local state and in the quiescent state
obtained from $m$ by emptying the name and polarity stacks and pushing onto the occurrence
stack the entry of the occurrence $(x, b, n, n + 1)$: the polarity marker of $b$ above the
name bits of $x$ above $n$ units.
