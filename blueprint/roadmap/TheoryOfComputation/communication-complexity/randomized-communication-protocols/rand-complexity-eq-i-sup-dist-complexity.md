# Yao's minimax principle for communication complexity

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A (deterministic) protocol is a finite binary tree whose leaves carry output bits and whose internal nodes are owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$; on inputs $(x, y)$ the run follows the announced bits from the root to a leaf, whose bit is the output, and the depth is the maximal number of bits announced along a root-to-leaf path. A randomized protocol is a finitely supported probability distribution $\pi$ on protocols (weights $\pi(p) \ge 0$, finitely many nonzero, summing to $1$); its cost is the maximal depth of a protocol in its support, and its error for $f$ at $(x, y)$ is $\sum_p \pi(p)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. For $\varepsilon \in \mathbb{R}$, the randomized communication complexity $R_\varepsilon(f)$ is the least $c \in \mathbb{N}$ such that some randomized protocol of cost at most $c$ has error at most $\varepsilon$ for $f$ on every input pair, and $0$ if there is none. For a probability distribution $\mu$ on $X \times Y$ and a protocol $p$, the distributional error of $p$ for $f$ is $\sum_{(x, y)} \mu(x, y)\, e_p(x, y)$, where $e_p(x, y)$ is $0$ if $p$ outputs $f(x, y)$ on $(x, y)$ and $1$ otherwise. The distributional complexity $D^\mu_\varepsilon(f)$ is the least $c \in \mathbb{N}$ such that some protocol of depth at most $c$ has distributional error at most $\varepsilon$, and $0$ if there is none. For every $f : X \times Y \to \{0, 1\}$ and every $\varepsilon \ge 0$,

$$R_\varepsilon(f) = \sup_\mu D^\mu_\varepsilon(f),$$

the supremum over all probability distributions $\mu$ on $X \times Y$.

## Informally uses

- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/matrix-game-minimax.md): Rao and Yehudayoff prove Theorem 3.3 from it (their Theorem 3.4), for the game whose rows are deterministic protocols and whose columns are inputs.
- [Distributional complexity is at most randomized complexity](dist-complexity-le-rand-complexity.md): the easy inequality, by averaging over the protocols in the support.

## Background

- [Yao's minimax principle](../../randomized-and-quantum-complexity/yao-s-minimax-principle/yao-minimax.md): the same exchange of minimum and maximum for an arbitrary finite cost matrix.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 3.3, proved there from von Neumann's minimax theorem.
