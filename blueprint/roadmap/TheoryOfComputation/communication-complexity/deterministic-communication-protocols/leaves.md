# Leaves of a protocol tree

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The set of leaves of a protocol, each leaf written as the list of bits announced along its
root-to-leaf path, is defined recursively: for a leaf it is the set containing only the empty list; for an
Alice or Bob node with children $p_0$ and $p_1$ it is the union of the lists $0\pi$ for $\pi$ a leaf of $p_0$
and the lists $1\pi$ for $\pi$ a leaf of $p_1$.
