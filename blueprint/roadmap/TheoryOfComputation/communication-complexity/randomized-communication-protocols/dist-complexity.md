# Distributional communication complexity

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. For a probability distribution $\mu$ on $X \times Y$ and a protocol $p$, the distributional error of $p$ for $f$ is $\sum_{(x, y)} \mu(x, y)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. For $f : X \times Y \to \{0, 1\}$, a probability distribution $\mu$ on $X \times Y$ and
$\varepsilon \in \mathbb{R}$, the distributional complexity $D^\mu_\varepsilon(f)$ is the least $c \in \mathbb{N}$
such that some protocol of depth at most $c$ has distributional error at most $\varepsilon$ under $\mu$. For
$\varepsilon \ge 0$ such a protocol exists; if none exists (for $\varepsilon < 0$) the value is $0$ by
convention.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3 ("average-case" error).
