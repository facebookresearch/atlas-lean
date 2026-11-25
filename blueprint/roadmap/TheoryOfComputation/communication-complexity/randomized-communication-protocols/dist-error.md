# Distributional error of a deterministic protocol

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. For a probability distribution $\mu$ on $X \times Y$, a protocol $p$ and $f : X \times Y \to \{0, 1\}$,
the distributional error of $p$ for $f$ under $\mu$ is $\sum_{(x, y) \in X \times Y} \mu(x, y)\, e_p(x, y)$,
where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise: the probability under $\mu$
that $p$ answers wrongly.
