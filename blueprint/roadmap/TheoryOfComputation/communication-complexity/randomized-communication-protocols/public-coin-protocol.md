# Public-coin randomized protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. For a set $R$ of random strings, a public-coin protocol is a family $(p_r)_{r \in R}$ of protocols, one
for each value $r$ of the shared random string; in use, $r$ is drawn uniformly from a finite set $R$,
independently of the inputs.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3.
