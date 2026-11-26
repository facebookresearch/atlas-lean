# Randomized communication complexity

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A randomized protocol is a finitely supported probability distribution $\pi$ on protocols (weights $\pi(p) \ge 0$, finitely many nonzero, summing to $1$); its cost is the maximal depth of a protocol in its support, and its error for $f$ at $(x, y)$ is $\sum_p \pi(p)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. For $f : X \times Y \to \{0, 1\}$ and $\varepsilon \in \mathbb{R}$, the randomized communication complexity
$R_\varepsilon(f)$ is the least $c \in \mathbb{N}$ such that some randomized protocol of cost at most $c$ has error
at most $\varepsilon$ for $f$ on every input pair. If there is no such protocol (for instance when
$\varepsilon < 0$), the value is $0$ by convention; for finite $X$, $Y$ and $\varepsilon \ge 0$ one exists.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 3 ("worst-case" error).
