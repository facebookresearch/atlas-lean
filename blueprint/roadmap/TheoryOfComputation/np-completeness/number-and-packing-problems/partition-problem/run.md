# Linear step bound for the PARTITION doubling machine

For every bitstring $x$ and every Boolean $v$, the [doubling machine](prog.md) started at label
$\mathsf{scan}(\text{start})$ with internal state $v$, with $x$ on the input stack $X$ and the
other stacks empty, reaches the label $\mathsf{done}$ in at most $4|x| + 2$ steps, with some
internal state and stack contents in which the output stack $O$ holds the
[doubling pass](transform.md) of $x$ from phase start.
