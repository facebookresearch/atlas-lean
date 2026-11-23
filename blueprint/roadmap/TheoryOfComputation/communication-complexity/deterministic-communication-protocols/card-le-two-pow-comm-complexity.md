# Fooling-set lower bound for the communication complexity

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. The deterministic communication complexity $D(f)$ is the least depth of a protocol computing $f$, and $0$ if no protocol computes $f$. A finite set $S \subseteq X \times Y$ is a fooling set for $f$ with value $b \in \{0, 1\}$ if $f(x, y) = b$ for all $(x, y) \in S$ and, for any two distinct pairs $(x_1, y_1), (x_2, y_2) \in S$, $f(x_1, y_2) \ne b$ or $f(x_2, y_1) \ne b$. If $f : X \times Y \to \{0, 1\}$ has a fooling set $S$ with some value $b$, then
$|S| \le 2^{D(f)}$, that is, $D(f) \ge \log_2 |S|$.

## Sources

- S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, web draft of 2007-01-08, Lemma 12.4.
