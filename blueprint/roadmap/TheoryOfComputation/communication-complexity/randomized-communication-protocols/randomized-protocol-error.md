# Error of a randomized protocol

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. For a randomized protocol $\pi$ (a finitely supported probability distribution on protocols), a function
$f : X \times Y \to \{0, 1\}$ and $(x, y)$, the error of $\pi$ is $\sum_p \pi(p)\, e_p(x, y)$, where $e_p(x, y)$ is
$0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise: the probability that the drawn protocol answers
wrongly.
