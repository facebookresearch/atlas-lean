# Communication cost of a protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is defined recursively: a leaf has depth $0$, and an Alice or Bob node with
children $p_0, p_1$ has depth $\max(\operatorname{depth} p_0, \operatorname{depth} p_1) + 1$. It is the largest number of
bits exchanged on any root-to-leaf path.
