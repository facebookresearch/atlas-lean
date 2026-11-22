# Transcript of a protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The transcript of a protocol on $(x, y)$ is defined recursively: it is the empty list for a leaf; for an
Alice node with map $a$ and children $p_0, p_1$ it is the bit $a(x)$ followed by the transcript of
$p_{a(x)}$ on $(x, y)$; for a Bob node with map $g$ it is $g(y)$ followed by the transcript of $p_{g(y)}$.
It names the root-to-leaf path that the run follows.
