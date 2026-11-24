# Output of a protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached.

Formally, the output of a leaf labelled $b$ is $b$; the output of an Alice node with map $a$ and children
$p_0, p_1$ on $(x, y)$ is the output of $p_{a(x)}$ on $(x, y)$; and that of a Bob node with map $g$ is the
output of $p_{g(y)}$ on $(x, y)$.
