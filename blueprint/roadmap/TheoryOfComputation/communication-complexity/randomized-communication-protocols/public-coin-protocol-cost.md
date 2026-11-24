# Cost of a public-coin protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. Let $R$ be a finite set. The cost of a public-coin protocol $(p_r)_{r \in R}$ is the maximum over $r \in R$
of the depth of $p_r$ (and $0$ if $R$ is empty).
