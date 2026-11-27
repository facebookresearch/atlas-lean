# Distributional complexity is at most randomized complexity

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A randomized protocol is a finitely supported probability distribution $\pi$ on protocols (weights $\pi(p) \ge 0$, finitely many nonzero, summing to $1$); its cost is the maximal depth of a protocol in its support, and its error for $f$ at $(x, y)$ is $\sum_p \pi(p)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. For $\varepsilon \in \mathbb{R}$, the randomized communication complexity $R_\varepsilon(f)$ is the least $c \in \mathbb{N}$ such that some randomized protocol of cost at most $c$ has error at most $\varepsilon$ for $f$ on every input pair, and $0$ if there is none. For a probability distribution $\mu$ on $X \times Y$ and a protocol $p$, the distributional error of $p$ for $f$ is $\sum_{(x, y)} \mu(x, y)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. The distributional complexity $D^\mu_\varepsilon(f)$ is the least $c \in \mathbb{N}$ such that some protocol of depth at most $c$ has distributional error at most $\varepsilon$, and $0$ if there is none. For every $f : X \times Y \to \{0, 1\}$, every probability distribution $\mu$ on
$X \times Y$ and every $\varepsilon \ge 0$, $D^\mu_\varepsilon(f) \le R_\varepsilon(f)$.

Some protocol in the support of an optimal randomized protocol has $\mu$-error at most $\varepsilon$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.3 (the easy direction).
