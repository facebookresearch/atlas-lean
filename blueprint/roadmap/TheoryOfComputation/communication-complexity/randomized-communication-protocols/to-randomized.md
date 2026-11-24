# A public-coin protocol as a randomized protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. Let $R$ be a nonempty finite set. The randomized protocol defined by a public-coin protocol $(p_r)_{r \in
R}$ is the image of the uniform distribution on $R$ under $r \mapsto p_r$: it gives each protocol $p$ the
weight $|\{r : p_r = p\}|/|R|$.
