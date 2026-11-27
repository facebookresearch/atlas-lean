# Leaf rectangles are monochromatic

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The transcript of the run on $(x, y)$ is the list of bits announced. A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. Let $p$ compute $f : X \times Y \to \{0, 1\}$ and let $x, x' \in X$ and $y, y' \in Y$ be such that
the runs on $(x, y)$ and $(x', y')$ have the same transcript. Then $f(x, y') = f(x, y)$ and $f(x', y') =
f(x, y)$.

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 1.7.
