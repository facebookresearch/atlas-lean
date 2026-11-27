# Walk-on step with the counter exhausted

Let $k$ be a stack, $\ell$ a label and $a, b$
bits. If stack $k$ of stacks $S$ is empty, then executing the walk-on block for counter $k$,
label $\ell$ and held color $(a, b)$, from any internal value and the stacks $S$, has the same
outcome as executing, from internal value false and the stacks $S$, the color-moving block
that continues to the rejecting label if the color it moves is $(a, b)$ and to the label that
restores the color stack otherwise.
