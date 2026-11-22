# Error probability of a public-coin protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. Let $R$ be a nonempty finite set and $(p_r)_{r \in R}$ a public-coin protocol. For $f : X \times Y \to
\{0, 1\}$ and $(x, y) \in X \times Y$, the error probability is the rational number

$$\frac{|\{r \in R : \text{the output of } p_r \text{ on } (x, y) \text{ differs from } f(x, y)\}|}{|R|},$$

the probability of an error when $r$ is uniform on $R$.
