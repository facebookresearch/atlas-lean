# Root of a variable

In Cooper's construction, the root of a variable $x$ in a state is the node recorded for $x$, if there is one, with the state unchanged; otherwise a fresh root node (no parents, true with probability $1/2$) is appended, recorded as the root of $x$, and returned, its index being the number of nodes before it was added.
