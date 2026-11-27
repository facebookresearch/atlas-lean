# Deterministic communication complexity of equality

For $n \in \mathbb{N}$, the equality function $\mathrm{EQ}_n : \{0,1\}^n \times \{0,1\}^n \to \{0, 1\}$ is $1$ exactly on pairs $(x, y)$ with $x = y$. Here protocols have inputs $X = Y = \{0,1\}^n$. A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. The deterministic communication complexity $D(f)$ is the least depth of a protocol computing $f$, and $0$ if no protocol computes $f$. For every $n \ge 1$, $D(\mathrm{EQ}_n) = n + 1$.

## Background

- [Error of the random-hash protocol for equality](../randomized-communication-protocols/error-prob-eq-hash-protocol-of-ne.md): with shared randomness, $k + 1$ bits suffice for error $2^{-k}$, independently of $n$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 1.14, with the trivial protocol for the upper bound.
