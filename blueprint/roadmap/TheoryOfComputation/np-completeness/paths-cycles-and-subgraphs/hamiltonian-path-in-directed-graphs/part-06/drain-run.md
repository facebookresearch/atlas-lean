# Draining a counter

Let $k$ be a stack of the emitter and $\ell, \ell'$ labels such that
the instruction at $\ell$ is the transfer loop that pops stack $k$ until it is empty, pushing
nothing, and then goes to $\ell'$. If $S$ is an assignment of stack contents in which stack $k$
consists of $n$ copies of a symbol $u$, then for every state bit $b$ the emitter goes in exactly
$n + 1$ steps from label $\ell$ with state bit $b$ and stacks $S$ to label $\ell'$ with state bit
false and the stacks $S$ with stack $k$ emptied.
