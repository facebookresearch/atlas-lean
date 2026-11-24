# The checking run

For every bit list $x$, the checking machine, started at the label
$\mathsf{dupP}$ with internal state false, with $x$ on its input stack $X$ and every other stack
empty, reaches the label $\mathsf{done}$ within $33(|x| + 1)^2$ steps, with some internal state
and stacks in which the output stack $O$ holds the answer of the checking machine on $x$.
