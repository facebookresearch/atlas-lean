# Restoring the color stack in the 3-COLOR verifier

Let $\mathit{pre}$ and $\mathit{post}$
be lists of pairs of bits, let $s$ be a Boolean state, and let $S$ assign to each stack a list of
symbols. Suppose that in $S$ the stack $P$ holds the bits of the flattening of $\mathit{post}$
and the stack $T$ holds the bits of the flattening of $\mathit{pre}$ in reverse order (as bit
symbols, top first). Then the verifier program runs in exactly $2 |\mathit{pre}| + 1$ steps from
the label back with state $s$ and stacks $S$ to the label edge with some state $s'$ and stacks
$S'$ such that $T$ is empty in $S'$, $P$ holds the bits of the flattening of $\mathit{pre}$
followed by $\mathit{post}$, and every stack other than $T$ and $P$ is unchanged.
