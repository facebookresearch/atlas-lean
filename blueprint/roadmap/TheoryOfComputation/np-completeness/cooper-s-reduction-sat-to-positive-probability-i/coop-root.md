# Root of a variable

In Cooper's construction, the root of a variable $x$ in a state is the node of the first pair $(x, v)$ in the state's list of recorded (variable, node) pairs, if there is one, with the state unchanged; otherwise a fresh root node (no parents, true with probability $1/2$) is appended, recorded as the root of $x$, and returned, its index being the number of nodes before it was added.

The definition applies to any state; it does not assume that each variable is recorded only once. If the list is $[(1, 0), (1, 1)]$, the root of variable $1$ is node $0$.
