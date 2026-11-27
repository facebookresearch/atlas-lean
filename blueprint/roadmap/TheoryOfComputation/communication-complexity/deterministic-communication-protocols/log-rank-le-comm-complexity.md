# Log-rank lower bound

Let $X$ and $Y$ be finite sets (the inputs of Alice and of Bob). A protocol is a finite binary tree whose leaves are labelled by bits and whose internal nodes are each owned by Alice, labelled by a map $X \to \{0, 1\}$, or by Bob, labelled by a map $Y \to \{0, 1\}$, with a $0$-child and a $1$-child. On inputs $(x, y)$ the run starts at the root; at an Alice node with map $a$ the bit $a(x)$ is announced and the run moves to the child with that bit, at a Bob node with map $b$ the bit $b(y)$ is announced likewise; the output is the label of the leaf reached. The depth of a protocol is the maximal number of bits announced along a root-to-leaf path ($0$ for a leaf). A protocol computes $f : X \times Y \to \{0, 1\}$ if its output on every $(x, y)$ is $f(x, y)$. The deterministic communication complexity $D(f)$ is the least depth of a protocol computing $f$, and $0$ if no protocol computes $f$. For a field $K$, the communication matrix $M_f$ of $f$ over $K$ is the $X \times Y$ matrix with entry $1$ at $(x, y)$ if $f(x, y) = 1$ and $0$ otherwise. For every field $K$ and every $f : X \times Y \to \{0, 1\}$,
$\lceil \log_2 \operatorname{rank}_K M_f \rceil \le D(f)$, where $\lceil \log_2 r \rceil$ denotes the least $k \in
\mathbb{N}$ with $r \le 2^k$ (so $0$ for $r \le 1$).

## Sources

- A. Rao and A. Yehudayoff, *Communication Complexity*, early draft, Theorem 2.11: "If a matrix has rank $r$, then its communication complexity is at least $\log r$".
