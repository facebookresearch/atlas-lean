# Running time and output of the marking machine

For every bit string $x$, the marking
machine started at its start label, with any flag, with $x$ on the input stack $X$ as bit symbols
and every other stack empty, reaches the label `done` within $8(|x| + 1)^4$ steps, with the
output stack $O$ holding exactly one entry: the answer of the marking algorithm on $x$.
