# Error indicator of a protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. For a protocol $p$, a function $f : X \times Y \to \{0, 1\}$ and $(x, y) \in X \times Y$, the error indicator
$e_p(x, y) \in \mathbb{R}$ is $0$ if the output of $p$ on $(x, y)$ is $f(x, y)$ and $1$ otherwise.
