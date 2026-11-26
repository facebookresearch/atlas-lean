# Deterministic communication complexity

Let $X$ and $Y$ be sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. For $f : X \times Y \to \{0, 1\}$, the deterministic communication complexity $D(f)$ is the least
depth of a protocol computing $f$. If no protocol computes $f$ (possible only for infinite input sets), the
value is $0$ by convention. For finite $X$ and $Y$ some protocol always computes $f$.

## Sources

- A. C. Yao, "Some complexity questions related to distributive computing", *Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing (STOC 1979)*, 209–213.
- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Chapter 1.
